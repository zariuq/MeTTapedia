import Mettapedia.GSLT.LanguageDef.M0GCLogicalReplayCanary
import Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy

/-!
# Semantic specification of the M0GC term-identifier matcher

The generated C checker does not allocate an instantiated source term.  It
walks a physical template and a certificate term in lockstep.  A template
variable succeeds only when the concrete certificate term identifier is the
identifier supplied for that variable; an application succeeds by comparing
symbol and arity fields and recursively matching ordered child identifiers.

This module models that allocation-free algorithm independently of logical
template instantiation.  It also gives certificate term tables an executable
`Pattern` reading.  The intended adequacy theorem is one-sided without an
extra canonical-heap condition: identifier matching implies structural
matching, while two distinct identifiers may reconstruct the same pattern.

Maturity boundary: this recursive identifier/table walk is a fully connected
model of the current custom M0GC proof of concept, not an endgame performance
or wire-layout decision.  The adequacy result is stated through decoded
templates and loaded term meanings so an optimized generated matcher can
replace this mechanism without changing its semantic obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCIdentifierMatcherAdequacy

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplay
open Mettapedia.GSLT.LanguageDef.M0GCTemplateAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy

@[simp] theorem applicationKind_ne_variableKind :
    applicationKind ≠ variableKind := by
  decide

@[simp] theorem variableKind_ne_applicationKind :
    variableKind ≠ applicationKind := by
  decide

/-! ## Independent meaning of the certificate ground-term table -/

mutual

/-- Reconstruct one certificate term by following its physical child
identifiers.  Fuel rejects cyclic or adversarial raw tables independently of
the chronological checks performed by the certificate loader. -/
def decodeGroundTerm? (profile : RuntimeProfile) (certificate : Certificate) :
    Nat → UInt32 → Option Pattern
  | 0, _ => none
  | fuel + 1, termId => do
      let node ← certificate.terms[termId.toNat]?
      let symbol ← profile.symbols[node.symbol.toNat]?
      if node.arity = symbol.arity then
        let childIds ← checkedSlice? certificate.children
          node.childStart.toNat node.arity.toNat
        let children ← decodeGroundTerms? profile certificate fuel childIds
        some (.apply symbol.name children)
      else none

/-- Reconstruct an ordered vector of certificate term identifiers. -/
def decodeGroundTerms? (profile : RuntimeProfile) (certificate : Certificate)
    (fuel : Nat) : List UInt32 → Option (List Pattern)
  | [] => some []
  | termId :: termIds => do
      let head ← decodeGroundTerm? profile certificate fuel termId
      let tail ← decodeGroundTerms? profile certificate fuel termIds
      some (head :: tail)

end

/-! ## Extensional model of a loaded term table -/

/-- Pointwise evidence carried by a successful `resolveIds?` traversal. -/
theorem resolveIds?_getElem?
    {α : Type*} {values : Array α} {ids : List UInt32} {resolved : List α}
    (allResolved : resolveIds? values ids = some resolved)
    {index : Nat} {id : UInt32} (idAt : ids[index]? = some id) :
    ∃ value, resolved[index]? = some value ∧
      values[id.toNat]? = some value := by
  induction ids generalizing resolved index with
  | nil => simp at idAt
  | cons head tail inductionHypothesis =>
      unfold resolveIds? at allResolved
      cases headResolved : values[head.toNat]? with
      | none => simp [headResolved] at allResolved
      | some headValue =>
          cases tailResolved : resolveIds? values tail with
          | none => simp [headResolved, tailResolved] at allResolved
          | some tailValues =>
              simp [headResolved, tailResolved] at allResolved
              subst resolved
              cases index with
              | zero =>
                  simp at idAt
                  subst id
                  exact ⟨headValue, rfl, headResolved⟩
              | succ index =>
                  simp at idAt
                  obtain ⟨value, valueAt, sourceAt⟩ :=
                    inductionHypothesis tailResolved idAt
                  exact ⟨value, by simpa using valueAt, sourceAt⟩

/-- Resolution preserves the exact physical vector length. -/
theorem resolveIds?_length_of_some
    {α : Type*} {values : Array α} {ids : List UInt32} {resolved : List α}
    (allResolved : resolveIds? values ids = some resolved) :
    resolved.length = ids.length := by
  induction ids generalizing resolved with
  | nil =>
      simp [resolveIds?] at allResolved
      subst resolved
      rfl
  | cons id ids inductionHypothesis =>
      cases headEq : values[id.toNat]? with
      | none => simp [resolveIds?, headEq] at allResolved
      | some head =>
          cases tailEq : resolveIds? values ids with
          | none => simp [resolveIds?, headEq, tailEq] at allResolved
          | some tail =>
              simp [resolveIds?, headEq, tailEq] at allResolved
              subst resolved
              simp [inductionHypothesis tailEq]

/-- Pointwise argument admissibility is preserved by physical identifier
resolution.  This is phrased over arbitrary arrays so the whole native replay
loop can reuse it for both explicit arguments and prior proof results. -/
theorem resolveIds?_argumentValidAt_zero
    {values : Array Pattern} {ids : List UInt32} {resolved : List Pattern}
    (allValid : ∀ {index : Nat} {value : Pattern},
      values[index]? = some value → argumentValidAt 0 value = true)
    (allResolved : resolveIds? values ids = some resolved) :
    ∀ value ∈ resolved, argumentValidAt 0 value = true := by
  induction ids generalizing resolved with
  | nil =>
      simp [resolveIds?] at allResolved
      subst resolved
      simp
  | cons id ids inductionHypothesis =>
      cases headEq : values[id.toNat]? with
      | none => simp [resolveIds?, headEq] at allResolved
      | some head =>
          cases tailEq : resolveIds? values ids with
          | none => simp [resolveIds?, headEq, tailEq] at allResolved
          | some tail =>
              simp [resolveIds?, headEq, tailEq] at allResolved
              subst resolved
              intro value membership
              simp only [List.mem_cons] at membership
              rcases membership with rfl | membership
              · exact allValid headEq
              · exact inductionHypothesis tailEq value membership

/-- An application whose children are admissible at depth zero is itself an
admissible rule argument. -/
theorem argumentValidAt_application_zero
    (constructor : String) (arguments : List Pattern)
    (allValid : ∀ argument ∈ arguments,
      argumentValidAt 0 argument = true) :
    argumentValidAt 0 (.apply constructor arguments) = true := by
  induction arguments with
  | nil =>
      simp [argumentValidAt, Pattern.isGroundAt, Pattern.isGroundListAt,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | cons argument arguments inductionHypothesis =>
      have headValid := allValid argument (by simp)
      have tailValid : ∀ tail ∈ arguments,
          argumentValidAt 0 tail = true := by
        intro tail membership
        exact allValid tail (by simp [membership])
      have tailApplication := inductionHypothesis tailValid
      simp only [argumentValidAt, Pattern.isGroundAt,
        Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true]
        at headValid tailApplication ⊢
      exact ⟨⟨headValid.1, tailApplication.1⟩,
        ⟨headValid.2, tailApplication.2⟩⟩

/-- A vector of depth-zero formals admits exactly an equally long vector of
admissible ground arguments. -/
theorem argumentsValidAt_map_zero
    (names : List String) (arguments : List Pattern)
    (sameLength : arguments.length = names.length)
    (allValid : ∀ argument ∈ arguments,
      argumentValidAt 0 argument = true) :
    argumentsValidAt (names.map fun name => (name, 0)) arguments = true := by
  induction names generalizing arguments with
  | nil =>
      cases arguments with
      | nil => rfl
      | cons argument arguments => simp at sameLength
  | cons name names inductionHypothesis =>
      cases arguments with
      | nil => simp at sameLength
      | cons argument arguments =>
          have headValid := allValid argument (by simp)
          have tailValid : ∀ tail ∈ arguments,
              argumentValidAt 0 tail = true := by
            intro tail membership
            exact allValid tail (by simp [membership])
          have tailLength : arguments.length = names.length := by
            simpa using Nat.succ.inj sameLength
          simp only [List.map_cons, argumentsValidAt, Bool.and_eq_true]
          exact ⟨headValid,
            inductionHypothesis arguments tailLength tailValid⟩

/-- A semantic realization of every raw certificate term identifier in one
array of `Pattern`s.  Each identifier must denote the application named by
its symbol profile to the denotations of its ordered physical children.

This contract deliberately does not require unique identifiers for equal
patterns.  Canonicality is a separate condition needed only for reflection. -/
structure GroundTermTableModel (profile : RuntimeProfile)
    (certificate : Certificate) (denotations : Array Pattern) : Prop where
  nodeMeaning : ∀ {termId : UInt32} {node : TermNode},
    certificate.terms[termId.toNat]? = some node →
    ∃ symbol childIds childPatterns,
      profile.symbols[node.symbol.toNat]? = some symbol ∧
      node.arity = symbol.arity ∧
      checkedSlice? certificate.children node.childStart.toNat
          node.arity.toNat = some childIds ∧
      resolveIds? denotations childIds = some childPatterns ∧
      denotations[termId.toNat]? =
        some (.apply symbol.name childPatterns)

/-- An existing array lookup is preserved when a later chronological value is
appended. -/
private theorem getElem?_push_of_some
    {α : Type*} {values : Array α} {index : Nat} {value extra : α}
    (resolved : values[index]? = some value) :
    (values.push extra)[index]? = some value := by
  have indexLt : index < values.size :=
    (Array.getElem?_eq_some_iff.mp resolved).choose
  have indexNe : index ≠ values.size := Nat.ne_of_lt indexLt
  simpa [Array.getElem?_push, indexNe] using resolved

/-- Resolving a chronological identifier vector is stable under appending a
later table entry. -/
private theorem resolveIds?_push_of_some
    {α : Type*} {values : Array α} {ids : List UInt32}
    {resolved : List α} (extra : α)
    (allResolved : resolveIds? values ids = some resolved) :
    resolveIds? (values.push extra) ids = some resolved := by
  induction ids generalizing resolved with
  | nil => simpa [resolveIds?] using allResolved
  | cons id ids inductionHypothesis =>
      cases headEq : values[id.toNat]? with
      | none => simp [resolveIds?, headEq] at allResolved
      | some head =>
          cases tailEq : resolveIds? values ids with
          | none => simp [resolveIds?, headEq, tailEq] at allResolved
          | some tail =>
              simp [resolveIds?, headEq, tailEq] at allResolved
              subst resolved
              have pushedHeadEq := getElem?_push_of_some headEq (extra := extra)
              have pushedTailEq := inductionHypothesis tailEq
              simp [resolveIds?, pushedHeadEq, pushedTailEq]

/-- Proof invariant for a physical prefix already consumed by the chronological
term loader.  The size equation makes the next pushed denotation correspond to
the next physical node, while `nodeMeaning` records every earlier application.
-/
private structure TermPrefixModel (profile : RuntimeProfile)
    (children : List UInt32) (nodes : List TermNode)
    (denotations : Array Pattern) : Prop where
  size_eq : denotations.size = nodes.length
  argumentValid : ∀ {termIndex : Nat} {pattern : Pattern},
    denotations[termIndex]? = some pattern →
      argumentValidAt 0 pattern = true
  nodeMeaning : ∀ {termIndex : Nat} {node : TermNode},
    nodes[termIndex]? = some node →
    ∃ symbol childIds childPatterns,
      profile.symbols[node.symbol.toNat]? = some symbol ∧
      node.arity = symbol.arity ∧
      checkedSlice? children node.childStart.toNat node.arity.toNat =
        some childIds ∧
      resolveIds? denotations childIds = some childPatterns ∧
      denotations[termIndex]? = some (.apply symbol.name childPatterns)

private theorem TermPrefixModel.empty
    (profile : RuntimeProfile) (children : List UInt32) :
    TermPrefixModel profile children [] #[] := by
  constructor
  · simp
  · intro termIndex pattern patternEq
    simp at patternEq
  · intro termIndex node nodeEq
    simp at nodeEq

/-- Extending a modeled prefix with the exact node admitted by the loader
preserves all earlier meanings and establishes the new final meaning. -/
private theorem TermPrefixModel.push
    {profile : RuntimeProfile} {children : List UInt32}
    {nodes : List TermNode} {denotations : Array Pattern}
    (prefixModel : TermPrefixModel profile children nodes denotations)
    {node : TermNode} {symbol : SymbolProfile} {childIds : List UInt32}
    {childPatterns : List Pattern}
    (symbolResolves : profile.symbols[node.symbol.toNat]? = some symbol)
    (arityMatches : node.arity = symbol.arity)
    (sliceResolves :
      checkedSlice? children node.childStart.toNat node.arity.toNat =
        some childIds)
    (patternsResolve : resolveIds? denotations childIds = some childPatterns) :
    TermPrefixModel profile children (nodes ++ [node])
      (denotations.push (.apply symbol.name childPatterns)) := by
  constructor
  · simp [prefixModel.size_eq]
  · intro termIndex pattern patternEq
    by_cases inPrefix : termIndex < denotations.size
    · have termIndexNe : termIndex ≠ denotations.size :=
        Nat.ne_of_lt inPrefix
      have oldPatternEq : denotations[termIndex]? = some pattern := by
        simpa [Array.getElem?_push, termIndexNe] using patternEq
      exact prefixModel.argumentValid oldPatternEq
    · have termIndexLt : termIndex <
          (denotations.push (.apply symbol.name childPatterns)).size :=
        (Array.getElem?_eq_some_iff.mp patternEq).choose
      have termIndexEq : termIndex = denotations.size := by
        simp only [Array.size_push] at termIndexLt
        omega
      subst termIndex
      have patternIsNew : pattern = .apply symbol.name childPatterns := by
        simpa using patternEq.symm
      subst pattern
      apply argumentValidAt_application_zero
      exact resolveIds?_argumentValidAt_zero
        prefixModel.argumentValid patternsResolve
  · intro termIndex queriedNode queriedNodeEq
    by_cases inPrefix : termIndex < nodes.length
    · have prefixNodeEq : nodes[termIndex]? = some queriedNode := by
        simpa [List.getElem?_append_left inPrefix] using queriedNodeEq
      obtain ⟨oldSymbol, oldChildIds, oldChildPatterns,
          oldSymbolEq, oldArityEq, oldSliceEq, oldChildrenEq,
          oldDenotationEq⟩ := prefixModel.nodeMeaning prefixNodeEq
      exact ⟨oldSymbol, oldChildIds, oldChildPatterns, oldSymbolEq,
        oldArityEq, oldSliceEq,
        resolveIds?_push_of_some _ oldChildrenEq,
        getElem?_push_of_some oldDenotationEq⟩
    · have termIndexLt : termIndex < (nodes ++ [node]).length :=
        (List.getElem?_eq_some_iff.mp queriedNodeEq).choose
      have termIndexEq : termIndex = nodes.length := by
        simp only [List.length_append, List.length_singleton] at termIndexLt
        omega
      subst termIndex
      have queriedNodeIsNew : queriedNode = node := by
        simpa using queriedNodeEq.symm
      subst queriedNode
      refine ⟨symbol, childIds, childPatterns, symbolResolves, arityMatches,
        sliceResolves, resolveIds?_push_of_some _ patternsResolve, ?_⟩
      rw [← prefixModel.size_eq]
      simp

/-- Successful chronological materialization extends any already modeled
prefix to a model of the entire consumed suffix. -/
private theorem materializeTermsLoop_buildsPrefix
    {profile : RuntimeProfile} {children : List UInt32}
    {processed remaining : List TermNode} {state final : TermState}
    (prefixModel : TermPrefixModel profile children processed state.patterns)
    (materialized :
      materializeTermsLoop profile children remaining state = some final) :
    TermPrefixModel profile children (processed ++ remaining) final.patterns := by
  induction remaining generalizing processed state final with
  | nil =>
      simp [materializeTermsLoop] at materialized
      subst final
      simpa using prefixModel
  | cons node nodes inductionHypothesis =>
      cases symbolEq : profile.symbols[node.symbol.toNat]? with
      | none => simp [materializeTermsLoop, symbolEq] at materialized
      | some symbol =>
          rw [materializeTermsLoop, symbolEq] at materialized
          dsimp at materialized
          by_cases arityEq : node.arity = symbol.arity
          · rw [if_pos arityEq] at materialized
            cases sliceEq : checkedSlice? children node.childStart.toNat
                node.arity.toNat with
            | none =>
                simp [sliceEq] at materialized
            | some childIds =>
                rw [sliceEq] at materialized
                dsimp at materialized
                cases patternsEq : resolveIds? state.patterns childIds with
                | none =>
                    simp [patternsEq] at materialized
                | some childPatterns =>
                    rw [patternsEq] at materialized
                    dsimp at materialized
                    cases hashesEq : resolveIds? state.hashes childIds with
                    | none =>
                        simp [hashesEq] at materialized
                    | some childHashes =>
                        rw [hashesEq] at materialized
                        dsimp at materialized
                        by_cases hashEq : node.termHash =
                            structuralTermHash node.symbol node.arity childHashes
                        · rw [if_pos hashEq] at materialized
                          have extended := prefixModel.push symbolEq arityEq
                            sliceEq patternsEq
                          have tailModel := inductionHypothesis extended materialized
                          simpa [List.append_assoc] using tailModel
                        · rw [if_neg hashEq] at materialized
                          contradiction
          · rw [if_neg arityEq] at materialized
            contradiction

/-- The abstract semantic table model required by the identifier matcher is
not an extra trust premise: every successful run of the actual M0GC
chronological term loader constructs it. -/
theorem materializeTerms?_groundTermTableModel
    {profile : RuntimeProfile} {certificate : Certificate} {state : TermState}
    (materialized : materializeTerms? profile certificate = some state) :
    GroundTermTableModel profile certificate state.patterns := by
  have loopMaterialized :
      materializeTermsLoop profile certificate.children certificate.terms {} =
        some state := by
    simpa [materializeTerms?] using materialized
  have prefixModel := materializeTermsLoop_buildsPrefix
    (TermPrefixModel.empty profile certificate.children) loopMaterialized
  refine { nodeMeaning := ?_ }
  intro termId node nodeEq
  simpa using prefixModel.nodeMeaning (termIndex := termId.toNat) nodeEq

/-- Every pattern reconstructed by the chronological M0GC term loader is an
admissible depth-zero proof argument.  No independent groundness assumption is
needed by the native replay soundness theorem. -/
theorem materializeTerms?_argumentValidAt_zero
    {profile : RuntimeProfile} {certificate : Certificate} {state : TermState}
    (materialized : materializeTerms? profile certificate = some state)
    {termIndex : Nat} {pattern : Pattern}
    (patternEq : state.patterns[termIndex]? = some pattern) :
    argumentValidAt 0 pattern = true := by
  have loopMaterialized :
      materializeTermsLoop profile certificate.children certificate.terms {} =
        some state := by
    simpa [materializeTerms?] using materialized
  have prefixModel := materializeTermsLoop_buildsPrefix
    (TermPrefixModel.empty profile certificate.children) loopMaterialized
  exact prefixModel.argumentValid patternEq

/-! ## Allocation-free identifier matcher -/

/-- The current generated C matcher enters at depth zero and rejects after
depth 1024, hence it admits exactly 1025 recursive matcher frames.  This
constant belongs to the connected proof-of-concept backend, not to the
logical template interface. -/
def nativeMatcherFuel : Nat := 1025

mutual

/-- A total, fail-closed specification of the generated C `match_template`
loop.  One unit of fuel corresponds to one permitted recursion depth; the C
entry call with `depth = 0` and rejection at `depth > 1024` is represented by
an initial fuel of `1025`.

The checked slices are redundant after successful certificate loading, but
make this standalone function total on arbitrary raw tables. -/
def matchTemplateId (tables : TemplateTables) (certificate : Certificate)
    (argumentIds : List UInt32) : Nat → UInt32 → UInt32 → Bool
  | 0, _, _ => false
  | fuel + 1, templateId, concreteId =>
      match tables.nodes[templateId.toNat]?,
          certificate.terms[concreteId.toNat]? with
      | some templateNode, some concreteNode =>
          if templateNode.kind = variableKind then
            match argumentIds[templateNode.value.toNat]? with
            | some argumentId => concreteId = argumentId
            | none => false
          else if templateNode.kind = applicationKind then
            if templateNode.value = concreteNode.symbol &&
                templateNode.arity = concreteNode.arity then
              match checkedSlice? tables.children
                      templateNode.childStart.toNat
                      templateNode.arity.toNat,
                    checkedSlice? certificate.children
                      concreteNode.childStart.toNat
                      concreteNode.arity.toNat with
              | some templateChildren, some concreteChildren =>
                  matchTemplateIds tables certificate argumentIds fuel
                    templateChildren concreteChildren
              | _, _ => false
            else false
          else false
      | _, _ => false

/-- Ordered lockstep matching for application children. -/
def matchTemplateIds (tables : TemplateTables) (certificate : Certificate)
    (argumentIds : List UInt32) (fuel : Nat) :
    List UInt32 → List UInt32 → Bool
  | [], [] => true
  | templateId :: templateIds, concreteId :: concreteIds =>
      matchTemplateId tables certificate argumentIds fuel
          templateId concreteId &&
        matchTemplateIds tables certificate argumentIds fuel
          templateIds concreteIds
  | _, _ => false

end

/-- The per-proof-step core of the generated C replay loop.  It checks the
physical rule/argument arities, walks every ordered premise template against
the corresponding concrete result-term identifier, and finally checks the
conclusion identifier. -/
def matchRuleIds (profile : RuntimeProfile) (tables : RuleTables)
    (certificate : Certificate) (argumentIds : List UInt32) (fuel : Nat)
    (ruleIndex : UInt16) (premiseConcreteIds : List UInt32)
    (conclusionConcreteId : UInt32) : Bool :=
  match profile.rules[ruleIndex.toNat]?, tables.layouts[ruleIndex.toNat]? with
  | some rule, some layout =>
      if argumentIds.length = rule.argumentCount.toNat then
        if premiseConcreteIds.length = rule.premiseCount.toNat then
          match checkedSlice? tables.premiseRoots layout.premiseStart.toNat
              rule.premiseCount.toNat with
          | some premiseRoots =>
              matchTemplateIds tables.templates certificate argumentIds fuel
                  premiseRoots premiseConcreteIds &&
                matchTemplateId tables.templates certificate argumentIds fuel
                  layout.conclusion conclusionConcreteId
          | none => false
        else false
      else false
  | _, _ => false

/-! ## Identifier matching is structurally sound -/

/-- For any semantic realization of the loaded term table, successful
identifier matching implies ordinary logical template instantiation.  The
mutual vector statement preserves child order and exposes the exact induction
used by the allocation-free loop. -/
theorem matchTemplateId_sound
    {profile : RuntimeProfile} {tables : TemplateTables}
    {certificate : Certificate} {denotations : Array Pattern}
    {argumentIds : List UInt32} {argumentPatterns : List Pattern}
    (model : GroundTermTableModel profile certificate denotations)
    (argumentsResolved :
      resolveIds? denotations argumentIds = some argumentPatterns) :
    ∀ fuel,
      (∀ templateId concreteId template concrete,
        matchTemplateId tables certificate argumentIds fuel
            templateId concreteId = true →
        decodeTemplate? profile tables fuel templateId = some template →
        denotations[concreteId.toNat]? = some concrete →
        instantiateTemplate? argumentPatterns template = some concrete) ∧
      (∀ templateIds concreteIds templates concretes,
        matchTemplateIds tables certificate argumentIds fuel
            templateIds concreteIds = true →
        decodeTemplates? profile tables fuel templateIds = some templates →
        resolveIds? denotations concreteIds = some concretes →
        instantiateTemplates? argumentPatterns templates = some concretes) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro templateId concreteId template concrete matched
          templateDecoded concreteResolved
        simp [matchTemplateId] at matched
      · intro templateIds concreteIds templates concretes matched
          templatesDecoded concretesResolved
        cases templateIds with
        | nil =>
            cases concreteIds with
            | nil =>
                simp [decodeTemplates?] at templatesDecoded
                simp [resolveIds?] at concretesResolved
                subst templates
                subst concretes
                simp [instantiateTemplates?]
            | cons concreteId concreteIds =>
                simp [matchTemplateIds] at matched
        | cons templateId templateIds =>
            cases concreteIds with
            | nil => simp [matchTemplateIds] at matched
            | cons concreteId concreteIds =>
                simp [matchTemplateIds, matchTemplateId] at matched
  | succ fuel inductionHypothesis =>
      rcases inductionHypothesis with
        ⟨smallerRootSound, smallerVectorSound⟩
      have rootSound : ∀ templateId concreteId template concrete,
          matchTemplateId tables certificate argumentIds (fuel + 1)
              templateId concreteId = true →
          decodeTemplate? profile tables (fuel + 1) templateId =
            some template →
          denotations[concreteId.toNat]? = some concrete →
          instantiateTemplate? argumentPatterns template = some concrete := by
        intro templateId concreteId template concrete matched
          templateDecoded concreteResolved
        cases templateNodeEq : tables.nodes[templateId.toNat]? with
        | none =>
            simp [matchTemplateId, templateNodeEq] at matched
        | some templateNode =>
            cases concreteNodeEq : certificate.terms[concreteId.toNat]? with
            | none =>
                simp [matchTemplateId, templateNodeEq, concreteNodeEq] at matched
            | some concreteNode =>
                by_cases isVariable : templateNode.kind = variableKind
                · cases argumentIdEq :
                    argumentIds[templateNode.value.toNat]? with
                  | none =>
                      simp [matchTemplateId, templateNodeEq, concreteNodeEq,
                        isVariable, argumentIdEq] at matched
                  | some argumentId =>
                      have concreteIdEq : concreteId = argumentId := by
                        simpa [matchTemplateId, templateNodeEq,
                          concreteNodeEq, isVariable, argumentIdEq] using
                          matched
                      have templateEq : template =
                          SchemaTemplate.variable templateNode.value.toNat := by
                        simpa [decodeTemplate?, templateNodeEq, isVariable]
                          using templateDecoded.symm
                      obtain ⟨argumentPattern, argumentPatternEq,
                          argumentDenotationEq⟩ :=
                        resolveIds?_getElem? argumentsResolved argumentIdEq
                      have argumentPatternIsConcrete :
                          argumentPattern = concrete := by
                        rw [concreteIdEq] at concreteResolved
                        exact Option.some.inj
                          (argumentDenotationEq.symm.trans concreteResolved)
                      subst template
                      subst concrete
                      simp [instantiateTemplate?, argumentPatternEq]
                · by_cases isApplication :
                    templateNode.kind = applicationKind
                  · by_cases symbolIndexMatches :
                      templateNode.value = concreteNode.symbol
                    · by_cases arityMatches :
                        templateNode.arity = concreteNode.arity
                      · cases templateChildrenEq : checkedSlice?
                          tables.children templateNode.childStart.toNat
                            templateNode.arity.toNat with
                        | none =>
                            have templateChildrenConcreteEq :
                                checkedSlice? tables.children
                                    templateNode.childStart.toNat
                                    concreteNode.arity.toNat = none := by
                              simpa [arityMatches] using templateChildrenEq
                            simp [matchTemplateId, templateNodeEq,
                              concreteNodeEq, isApplication,
                              symbolIndexMatches, arityMatches,
                              templateChildrenConcreteEq] at matched
                        | some templateChildren =>
                            have templateChildrenConcreteEq :
                                checkedSlice? tables.children
                                    templateNode.childStart.toNat
                                    concreteNode.arity.toNat =
                                  some templateChildren := by
                              simpa [arityMatches] using templateChildrenEq
                            cases concreteChildrenEq : checkedSlice?
                                certificate.children
                                concreteNode.childStart.toNat
                                concreteNode.arity.toNat with
                            | none =>
                                simp [matchTemplateId, templateNodeEq,
                                  concreteNodeEq, isApplication,
                                  symbolIndexMatches, arityMatches,
                                  templateChildrenConcreteEq,
                                  concreteChildrenEq] at matched
                            | some concreteChildren =>
                                have childrenMatched :
                                    matchTemplateIds tables certificate
                                      argumentIds fuel templateChildren
                                      concreteChildren = true := by
                                  simpa [matchTemplateId, templateNodeEq,
                                    concreteNodeEq, isApplication,
                                    symbolIndexMatches, arityMatches,
                                    templateChildrenConcreteEq,
                                    concreteChildrenEq]
                                    using matched
                                cases templateSymbolEq :
                                    profile.symbols[
                                      templateNode.value.toNat]? with
                                | none =>
                                    simp [decodeTemplate?, templateNodeEq,
                                      isApplication,
                                      templateSymbolEq] at templateDecoded
                                | some templateSymbol =>
                                    by_cases templateArityMatches :
                                        templateNode.arity =
                                          templateSymbol.arity
                                    · have templateChildrenSymbolEq :
                                          checkedSlice? tables.children
                                              templateNode.childStart.toNat
                                              templateSymbol.arity.toNat =
                                            some templateChildren := by
                                        simpa [templateArityMatches] using
                                          templateChildrenEq
                                      cases childTemplatesEq :
                                        decodeTemplates? profile tables fuel
                                          templateChildren with
                                      | none =>
                                          simp [decodeTemplate?,
                                            templateNodeEq,
                                            isApplication, templateSymbolEq,
                                            templateArityMatches,
                                            templateChildrenSymbolEq,
                                            childTemplatesEq] at templateDecoded
                                      | some childTemplates =>
                                          have templateEq : template =
                                              SchemaTemplate.application
                                                templateSymbol.name
                                                childTemplates := by
                                            simpa [decodeTemplate?,
                                              templateNodeEq,
                                              isApplication,
                                              templateSymbolEq,
                                              templateArityMatches,
                                              templateChildrenSymbolEq,
                                              childTemplatesEq] using
                                              templateDecoded.symm
                                          obtain ⟨concreteSymbol, childIds,
                                              childPatterns,
                                              concreteSymbolEq,
                                              concreteArityMatches,
                                              childIdsEq,
                                              childPatternsEq,
                                              concreteDenotationEq⟩ :=
                                            model.nodeMeaning concreteNodeEq
                                          have concreteChildrenAreChildIds :
                                              concreteChildren = childIds := by
                                            exact Option.some.inj
                                              (concreteChildrenEq.symm.trans
                                                childIdsEq)
                                          have symbolsEqual :
                                              templateSymbol =
                                                concreteSymbol := by
                                            rw [symbolIndexMatches] at templateSymbolEq
                                            exact Option.some.inj
                                              (templateSymbolEq.symm.trans
                                                concreteSymbolEq)
                                          have concreteEq : concrete =
                                              Pattern.apply concreteSymbol.name
                                                childPatterns := by
                                            exact Option.some.inj
                                              (concreteResolved.symm.trans
                                                concreteDenotationEq)
                                          have childrenInstantiate :=
                                            smallerVectorSound
                                              templateChildren childIds
                                              childTemplates childPatterns
                                              (by simpa
                                                [concreteChildrenAreChildIds]
                                                using childrenMatched)
                                              childTemplatesEq childPatternsEq
                                          subst template
                                          subst concrete
                                          subst concreteSymbol
                                          simp [instantiateTemplate?,
                                            childrenInstantiate]
                                    · simp [decodeTemplate?, templateNodeEq,
                                        isApplication,
                                        templateSymbolEq,
                                        templateArityMatches] at templateDecoded
                      · simp [matchTemplateId, templateNodeEq,
                          concreteNodeEq, isApplication,
                          symbolIndexMatches, arityMatches] at matched
                    · simp [matchTemplateId, templateNodeEq, concreteNodeEq,
                        isApplication, symbolIndexMatches] at matched
                  · simp [matchTemplateId, templateNodeEq, concreteNodeEq,
                      isVariable, isApplication] at matched
      have vectorSound : ∀ templateIds concreteIds templates concretes,
          matchTemplateIds tables certificate argumentIds (fuel + 1)
              templateIds concreteIds = true →
          decodeTemplates? profile tables (fuel + 1) templateIds =
            some templates →
          resolveIds? denotations concreteIds = some concretes →
          instantiateTemplates? argumentPatterns templates =
            some concretes := by
        intro templateIds
        induction templateIds with
        | nil =>
            intro concreteIds templates concretes matched templatesDecoded
              concretesResolved
            cases concreteIds with
            | nil =>
                simp [decodeTemplates?] at templatesDecoded
                simp [resolveIds?] at concretesResolved
                subst templates
                subst concretes
                simp [instantiateTemplates?]
            | cons concreteId concreteIds =>
                simp [matchTemplateIds] at matched
        | cons templateId templateIds vectorInduction =>
            intro concreteIds templates concretes matched templatesDecoded
              concretesResolved
            cases concreteIds with
            | nil => simp [matchTemplateIds] at matched
            | cons concreteId concreteIds =>
                have matchedParts :
                    matchTemplateId tables certificate argumentIds (fuel + 1)
                        templateId concreteId = true ∧
                      matchTemplateIds tables certificate argumentIds
                        (fuel + 1) templateIds concreteIds = true := by
                  simpa only [matchTemplateIds, Bool.and_eq_true] using matched
                cases headTemplateEq :
                    decodeTemplate? profile tables (fuel + 1) templateId with
                | none =>
                    simp [decodeTemplates?, headTemplateEq] at templatesDecoded
                | some headTemplate =>
                    cases tailTemplatesEq :
                        decodeTemplates? profile tables (fuel + 1)
                          templateIds with
                    | none =>
                        simp [decodeTemplates?, headTemplateEq,
                          tailTemplatesEq] at templatesDecoded
                    | some tailTemplates =>
                        simp [decodeTemplates?, headTemplateEq,
                          tailTemplatesEq] at templatesDecoded
                        subst templates
                        cases headConcreteEq :
                            denotations[concreteId.toNat]? with
                        | none =>
                            simp [resolveIds?, headConcreteEq] at concretesResolved
                        | some headConcrete =>
                            cases tailConcretesEq :
                                resolveIds? denotations concreteIds with
                            | none =>
                                simp [resolveIds?, headConcreteEq,
                                  tailConcretesEq] at concretesResolved
                            | some tailConcretes =>
                                simp [resolveIds?, headConcreteEq,
                                  tailConcretesEq] at concretesResolved
                                subst concretes
                                have headInstantiates := rootSound
                                  templateId concreteId headTemplate
                                  headConcrete matchedParts.1 headTemplateEq
                                  headConcreteEq
                                have tailInstantiates := vectorInduction
                                  concreteIds tailTemplates tailConcretes
                                  matchedParts.2 tailTemplatesEq
                                  tailConcretesEq
                                simp [instantiateTemplates?, headInstantiates,
                                  tailInstantiates]
      exact ⟨rootSound, vectorSound⟩

theorem matchTemplateId_sound_of_decode
    {profile : RuntimeProfile} {tables : TemplateTables}
    {certificate : Certificate} {denotations : Array Pattern}
    {argumentIds : List UInt32} {argumentPatterns : List Pattern}
    {fuel : Nat} {templateId concreteId : UInt32}
    {template : SchemaTemplate} {concrete : Pattern}
    (model : GroundTermTableModel profile certificate denotations)
    (argumentsResolved :
      resolveIds? denotations argumentIds = some argumentPatterns)
    (matched : matchTemplateId tables certificate argumentIds fuel
      templateId concreteId = true)
    (templateDecoded :
      decodeTemplate? profile tables fuel templateId = some template)
    (concreteResolved :
      denotations[concreteId.toNat]? = some concrete) :
    instantiateTemplate? argumentPatterns template = some concrete :=
  (matchTemplateId_sound model argumentsResolved fuel).1
    templateId concreteId template concrete matched templateDecoded
      concreteResolved

/-- A successful physical rule-step match is the ordinary logical rule-template
instantiation, once the actual chronological loader has supplied the term
meanings.  This is the rule-level correspondence theorem for the generated C
table walk; premise order and the conclusion remain separately observable. -/
theorem matchRuleIds_sound_of_decode
    {profile : RuntimeProfile} {tables : RuleTables}
    {certificate : Certificate} {state : TermState}
    {argumentIds : List UInt32} {argumentPatterns : List Pattern}
    {fuel : Nat} {ruleIndex : UInt16}
    {premiseConcreteIds : List UInt32} {conclusionConcreteId : UInt32}
    {template : RuleTemplate} {premises : List Pattern} {conclusion : Pattern}
    (materialized : materializeTerms? profile certificate = some state)
    (argumentsResolved :
      resolveIds? state.patterns argumentIds = some argumentPatterns)
    (physicalDecoded :
      decodeRuleTemplate? profile tables fuel ruleIndex = some template)
    (matched :
      matchRuleIds profile tables certificate argumentIds fuel ruleIndex
        premiseConcreteIds conclusionConcreteId = true)
    (premisesResolved :
      resolveIds? state.patterns premiseConcreteIds = some premises)
    (conclusionResolved :
      state.patterns[conclusionConcreteId.toNat]? = some conclusion) :
    template.instantiate? argumentPatterns = some (premises, conclusion) := by
  have model := materializeTerms?_groundTermTableModel materialized
  unfold matchRuleIds at matched
  unfold decodeRuleTemplate? at physicalDecoded
  cases ruleEq : profile.rules[ruleIndex.toNat]? with
  | none => simp [ruleEq] at matched
  | some rule =>
      cases layoutEq : tables.layouts[ruleIndex.toNat]? with
      | none => simp [ruleEq, layoutEq] at matched
      | some layout =>
          rw [ruleEq, layoutEq] at matched physicalDecoded
          dsimp at matched physicalDecoded
          by_cases argumentCountEq :
              argumentIds.length = rule.argumentCount.toNat
          · rw [if_pos argumentCountEq] at matched
            by_cases premiseCountEq :
                premiseConcreteIds.length = rule.premiseCount.toNat
            · rw [if_pos premiseCountEq] at matched
              cases rootsEq : checkedSlice? tables.premiseRoots
                  layout.premiseStart.toNat rule.premiseCount.toNat with
              | none =>
                  simp [rootsEq] at matched
              | some premiseRoots =>
                  rw [rootsEq] at matched physicalDecoded
                  dsimp at matched physicalDecoded
                  have matchedParts :
                      matchTemplateIds tables.templates certificate argumentIds
                          fuel premiseRoots premiseConcreteIds = true ∧
                        matchTemplateId tables.templates certificate argumentIds
                          fuel layout.conclusion conclusionConcreteId = true := by
                    simpa only [Bool.and_eq_true] using matched
                  cases premiseTemplatesEq :
                      decodeTemplates? profile tables.templates fuel premiseRoots with
                  | none =>
                      simp [premiseTemplatesEq] at physicalDecoded
                  | some premiseTemplates =>
                      rw [premiseTemplatesEq] at physicalDecoded
                      dsimp at physicalDecoded
                      cases conclusionTemplateEq :
                          decodeTemplate? profile tables.templates fuel
                            layout.conclusion with
                      | none =>
                          simp [conclusionTemplateEq] at physicalDecoded
                      | some conclusionTemplate =>
                          simp [conclusionTemplateEq] at physicalDecoded
                          subst template
                          have argumentPatternLength :
                              argumentPatterns.length =
                                rule.argumentCount.toNat :=
                            (resolveIds?_length_of_some argumentsResolved).trans
                              argumentCountEq
                          have premisesInstantiate :=
                            (matchTemplateId_sound model argumentsResolved fuel).2
                              premiseRoots premiseConcreteIds premiseTemplates
                              premises matchedParts.1 premiseTemplatesEq
                              premisesResolved
                          have conclusionInstantiates :=
                            (matchTemplateId_sound model argumentsResolved fuel).1
                              layout.conclusion conclusionConcreteId
                              conclusionTemplate conclusion matchedParts.2
                              conclusionTemplateEq conclusionResolved
                          simp [RuleTemplate.instantiate?, argumentPatternLength,
                            premisesInstantiate, conclusionInstantiates]
            · rw [if_neg premiseCountEq] at matched
              contradiction
          · rw [if_neg argumentCountEq] at matched
            contradiction

/-- The physical rule matcher is sound directly against the independently
validated source calculus when source compilation and physical decoding select
the same logical template. -/
theorem matchRuleIds_sound_against_source
    {definition : ValidatedCalculusLanguageDef}
    {profile : RuntimeProfile} {tables : RuleTables}
    {certificate : Certificate} {state : TermState}
    {argumentIds : List UInt32} {argumentPatterns : List Pattern}
    {fuel : Nat} {ruleIndex : UInt16}
    {premiseConcreteIds : List UInt32} {conclusionConcreteId : UInt32}
    {rule : RuleSchema} {template : RuleTemplate}
    {premises : List Pattern} {conclusion : Pattern}
    (materialized : materializeTerms? profile certificate = some state)
    (argumentsResolved :
      resolveIds? state.patterns argumentIds = some argumentPatterns)
    (sourceCompiled : compileRuleTemplate? rule = some template)
    (physicalDecoded :
      decodeRuleTemplate? profile tables fuel ruleIndex = some template)
    (matched :
      matchRuleIds profile tables certificate argumentIds fuel ruleIndex
        premiseConcreteIds conclusionConcreteId = true)
    (premisesResolved :
      resolveIds? state.patterns premiseConcreteIds = some premises)
    (conclusionResolved :
      state.patterns[conclusionConcreteId.toNat]? = some conclusion)
    (lookup : definition.1.lookupRule? rule.id = some rule)
    (argumentsValid :
      argumentsValidAt rule.metavariables argumentPatterns = true) :
    instantiateRule? definition
        { ruleId := rule.id, arguments := argumentPatterns } =
      some (premises, conclusion) := by
  rw [← RuleTemplate.instantiate_eq_source_rule sourceCompiled
    argumentPatterns lookup argumentsValid]
  exact matchRuleIds_sound_of_decode materialized argumentsResolved
    physicalDecoded matched premisesResolved conclusionResolved

/-! ## Discriminating examples -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplayCanary

def tables : TemplateTables :=
  Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy.pairTables

def ruleTables : RuleTables :=
  Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy.pairRuleTables

theorem pair_term_decodes :
    decodeGroundTerm? profile certificate 2 2 =
      some M0GCLogicalReplayCanary.pair := by
  simp [decodeGroundTerm?, decodeGroundTerms?, profile, certificate,
    leftNode, rightNode, pairNode, checkedSlice?,
    M0GCLogicalReplayCanary.pair, M0GCLogicalReplayCanary.left,
    M0GCLogicalReplayCanary.right]

theorem pair_identifier_match :
    matchTemplateId tables certificate [0, 1] 2 2 2 = true := by
  simp [matchTemplateId, matchTemplateIds, tables,
    Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy.pairTables,
    certificate, leftNode, rightNode, pairNode, checkedSlice?, variableKind,
    applicationKind]

theorem swapped_arguments_rejected :
    matchTemplateId tables certificate [1, 0] 2 2 2 = false := by
  simp [matchTemplateId, matchTemplateIds, tables,
    Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy.pairTables,
    certificate, leftNode, rightNode, pairNode, checkedSlice?, variableKind,
    applicationKind]

theorem pair_rule_decodes :
    decodeRuleTemplate? profile ruleTables 2 0 = some binaryTemplate := by
  simp [decodeRuleTemplate?, profile, pairRuleProfile, ruleTables,
    Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy.pairRuleTables,
    Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy.pairTables,
    binaryTemplate, decodeTemplate?, decodeTemplates?, checkedSlice?,
    variableKind, applicationKind]

theorem pair_rule_identifier_match :
    matchRuleIds profile ruleTables certificate [0, 1] 2 0 [] 2 = true := by
  simp [matchRuleIds, matchTemplateId, matchTemplateIds, profile,
    pairRuleProfile, ruleTables,
    Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy.pairRuleTables,
    Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy.pairTables,
    certificate, leftNode, rightNode, pairNode, checkedSlice?, variableKind,
    applicationKind]

theorem wrong_rule_premise_length_rejected :
    matchRuleIds profile ruleTables certificate [0, 1] 2 0 [0] 2 = false := by
  simp [matchRuleIds, profile, pairRuleProfile, ruleTables,
    Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy.pairRuleTables]

theorem wrong_rule_conclusion_identifier_rejected :
    matchRuleIds profile ruleTables certificate [0, 1] 2 0 [] 0 = false := by
  simp [matchRuleIds, matchTemplateId, matchTemplateIds, profile,
    pairRuleProfile, ruleTables,
    Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy.pairRuleTables,
    Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy.pairTables,
    certificate, leftNode, rightNode, pairNode, checkedSlice?, variableKind,
    applicationKind]

theorem pair_rule_identifier_match_is_source_rule :
    instantiateRule? definition
        { ruleId := ⟨"pair"⟩
          arguments :=
            [M0GCLogicalReplayCanary.left,
              M0GCLogicalReplayCanary.right] } =
      some ([], M0GCLogicalReplayCanary.pair) := by
  apply matchRuleIds_sound_against_source
    (state := termState) (argumentIds := [0, 1])
    (fuel := 2) (ruleIndex := 0) (premiseConcreteIds := [])
    (conclusionConcreteId := 2)
    (rule := InferenceCompiledPlanLowering.binaryRule)
    (template := binaryTemplate)
  · exact terms_materialize
  · rfl
  · exact compile_binaryRule
  · exact pair_rule_decodes
  · exact pair_rule_identifier_match
  · rfl
  · rfl
  · rfl
  · rfl

/-- A raw certificate table may contain two identifiers with the same
structural meaning.  The actual C matcher intentionally distinguishes them. -/
def duplicateLeftCertificate : Certificate :=
  { certificate with terms := [leftNode, rightNode, pairNode, leftNode] }

theorem duplicate_left_decodes_equal :
    decodeGroundTerm? profile duplicateLeftCertificate 2 0 =
      decodeGroundTerm? profile duplicateLeftCertificate 2 3 := by
  simp [decodeGroundTerm?, decodeGroundTerms?, profile,
    duplicateLeftCertificate, certificate, leftNode, checkedSlice?]

theorem duplicate_structural_argument_instantiates :
    instantiateFlatTemplate?
        profile tables
          [M0GCLogicalReplayCanary.left, M0GCLogicalReplayCanary.right]
          2 2 = some M0GCLogicalReplayCanary.pair := by
  simp [instantiateFlatTemplate?, instantiateFlatTemplates?, profile, tables,
    Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy.pairTables,
    checkedSlice?, variableKind, applicationKind,
    M0GCLogicalReplayCanary.left, M0GCLogicalReplayCanary.right,
    M0GCLogicalReplayCanary.pair]

theorem duplicate_identifier_not_interchangeable :
    matchTemplateId tables duplicateLeftCertificate [3, 1] 2 2 2 = false := by
  simp [matchTemplateId, matchTemplateIds, tables,
    Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy.pairTables,
    duplicateLeftCertificate, certificate, leftNode, rightNode, pairNode,
    checkedSlice?, variableKind, applicationKind]

end Canary

#print axioms Canary.pair_term_decodes
#print axioms Canary.pair_identifier_match
#print axioms Canary.swapped_arguments_rejected
#print axioms materializeTerms?_groundTermTableModel
#print axioms materializeTerms?_argumentValidAt_zero
#print axioms matchTemplateId_sound
#print axioms matchRuleIds_sound_of_decode
#print axioms matchRuleIds_sound_against_source
#print axioms Canary.pair_rule_identifier_match
#print axioms Canary.wrong_rule_premise_length_rejected
#print axioms Canary.wrong_rule_conclusion_identifier_rejected
#print axioms Canary.pair_rule_identifier_match_is_source_rule
#print axioms Canary.duplicate_left_decodes_equal
#print axioms Canary.duplicate_structural_argument_instantiates
#print axioms Canary.duplicate_identifier_not_interchangeable

end Mettapedia.GSLT.LanguageDef.M0GCIdentifierMatcherAdequacy
