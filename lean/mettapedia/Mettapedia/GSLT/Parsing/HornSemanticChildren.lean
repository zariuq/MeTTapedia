import Mettapedia.GSLT.Parsing.HornProgramChildren

/-!
# Semantic child reflection through compiler head matches

This module constructs the explicit unifier that relates a ground parser query
to a certificate-independent Horn specialization.  Together with the MGU and
range-safety results, it is the bridge from semantic recursive child calls to
the executable program-derived child universe.
-/

namespace Mettapedia.GSLT.Parsing.HornSemanticChildren

open HornCertificate HornUnification HornHeadEnumeration HornSpecialization
open HornSpecializationHead HornSpecializationBody HornProgramChildren

def semanticQuerySubstitution (substitution : SymbolicSubstitution)
    (input value output : Term) :
    Mettapedia.Logic.LP.Subst compilerSignature
  | scopedVariable =>
      match scopedVariable.origin with
      | .rule => symbolicLPSubstitution substitution scopedVariable
      | .query =>
          if scopedVariable.identifier = 0 then encodeScopedTerm .query input
          else if scopedVariable.identifier = 1 then encodeScopedTerm .query value
          else if scopedVariable.identifier = 2 then encodeScopedTerm .query output
          else .var scopedVariable

mutual
  theorem encodeScopedTerm_isGround_of_noVariables
      (origin : VariableOrigin) (source : Term)
      (noVariables : termVariables source = []) :
      (encodeScopedTerm origin source).isGround := by
    cases source with
    | var identifier => simp [termVariables] at noVariables
    | atom name => trivial
    | integer value => trivial
    | app constructor arguments =>
        simp only [termVariables] at noVariables
        simp only [encodeScopedTerm, Mettapedia.Logic.LP.Term.isGround]
        intro index
        exact encodeScopedTerms_areGround_of_noVariables origin arguments
          noVariables _ (List.get_mem _ index)

  theorem encodeScopedTerms_areGround_of_noVariables
      (origin : VariableOrigin) (sources : Terms)
      (noVariables : termsVariables sources = []) :
      ∀ term ∈ encodeScopedTerms origin sources, term.isGround := by
    cases sources with
    | nil => simp [encodeScopedTerms]
    | cons head tail =>
        have components := List.append_eq_nil_iff.mp noVariables
        simp only [encodeScopedTerms, List.mem_cons]
        intro term member
        rcases member with rfl | member
        · exact encodeScopedTerm_isGround_of_noVariables origin head components.1
        · exact encodeScopedTerms_areGround_of_noVariables origin tail
            components.2 term member
end

theorem semanticQuerySubstitution_apply_parserQuery
    (substitution : SymbolicSubstitution) (parseRelation : String)
    (grammar input value output : Term)
    (ground : termVariables grammar = []) :
    (semanticQuerySubstitution substitution input value output).applyAtom
        (encodeScopedAtom .query (parserQuery parseRelation grammar)) =
      encodeScopedAtom .query
        { relation := parseRelation
          arguments := Terms.ofList [grammar, input, value, output] } := by
  let candidate := semanticQuerySubstitution substitution input value output
  have grammarGround := encodeScopedTerm_isGround_of_noVariables
    .query grammar ground
  have grammarFixed := applyTerm_eq_self_of_isGround candidate grammarGround
  have argumentsEqual :
      (encodeScopedTerms .query
        (Terms.ofList [grammar, .var 0, .var 1, .var 2])).map
          candidate.applyTerm =
      encodeScopedTerms .query
        (Terms.ofList [grammar, input, value, output]) := by
    change [candidate.applyTerm (encodeScopedTerm .query grammar),
      candidate { origin := .query, identifier := 0 },
      candidate { origin := .query, identifier := 1 },
      candidate { origin := .query, identifier := 2 }] =
      [encodeScopedTerm .query grammar, encodeScopedTerm .query input,
        encodeScopedTerm .query value, encodeScopedTerm .query output]
    rw [grammarFixed]
    rfl
  simp only [Mettapedia.Logic.LP.Subst.applyAtom, encodeScopedAtom, parserQuery]
  congr 1
  funext index
  have pointwise := List.get_of_eq argumentsEqual
    (⟨index.val, by simp⟩ : Fin
      ((encodeScopedTerms .query
        (Terms.ofList [grammar, .var 0, .var 1, .var 2])).map
          candidate.applyTerm).length)
  simpa [candidate] using pointwise

mutual
  theorem semanticQuerySubstitution_apply_ruleTerm
      (substitution : SymbolicSubstitution) (input value output source : Term) :
      (semanticQuerySubstitution substitution input value output).applyTerm
          (encodeScopedTerm .rule source) =
        (symbolicLPSubstitution substitution).applyTerm
          (encodeScopedTerm .rule source) := by
    cases source with
    | var identifier => rfl
    | atom name => rfl
    | integer number => rfl
    | app constructor arguments =>
        have argumentsEqual := semanticQuerySubstitution_apply_ruleTerms
          substitution input value output arguments
        simp only [encodeScopedTerm, Mettapedia.Logic.LP.Subst.applyTerm]
        congr 1
        funext index
        have pointwise := List.get_of_eq argumentsEqual
          (⟨index.val, by simp⟩ :
            Fin ((encodeScopedTerms .rule arguments).map
              (semanticQuerySubstitution substitution input value output).applyTerm).length)
        simpa using pointwise

  theorem semanticQuerySubstitution_apply_ruleTerms
      (substitution : SymbolicSubstitution) (input value output : Term)
      (sources : Terms) :
      (encodeScopedTerms .rule sources).map
          (semanticQuerySubstitution substitution input value output).applyTerm =
        (encodeScopedTerms .rule sources).map
          (symbolicLPSubstitution substitution).applyTerm := by
    cases sources with
    | nil => rfl
    | cons head tail =>
        simp only [encodeScopedTerms, List.map_cons, List.cons.injEq]
        exact ⟨
          semanticQuerySubstitution_apply_ruleTerm substitution input value output
            head,
          semanticQuerySubstitution_apply_ruleTerms substitution input value output
            tail⟩
end

theorem semanticQuerySubstitution_apply_ruleAtom
    (substitution : SymbolicSubstitution) (input value output : Term)
    (source : Atom) :
    (semanticQuerySubstitution substitution input value output).applyAtom
        (encodeScopedAtom .rule source) =
      (symbolicLPSubstitution substitution).applyAtom
        (encodeScopedAtom .rule source) := by
  have argumentsEqual := semanticQuerySubstitution_apply_ruleTerms
    substitution input value output source.arguments
  simp only [Mettapedia.Logic.LP.Subst.applyAtom, encodeScopedAtom]
  congr 1
  funext index
  have pointwise := List.get_of_eq argumentsEqual
    (⟨index.val, by simp⟩ :
      Fin ((encodeScopedTerms .rule source.arguments).map
        (semanticQuerySubstitution substitution input value output).applyTerm).length)
  simpa using pointwise

theorem semanticSpecializationHead_unifies_parserQuery
    {parseRelation : String} {categories : CategoryTable}
    {rule : Rule} {substitution : SymbolicSubstitution}
    {head : Atom} {parsed : ParsedAtom}
    (instantiated : instantiateSymbolicAtom substitution rule.head = some head)
    (decoded : decodeParseAtom parseRelation categories head = some parsed) :
    ∃ input value output,
      (semanticQuerySubstitution substitution input value output).applyAtom
          (encodeScopedAtom .query
            (parserQuery parseRelation parsed.grammar)) =
        (semanticQuerySubstitution substitution input value output).applyAtom
          (encodeScopedAtom .rule rule.head) := by
  obtain ⟨input, value, output, arguments⟩ :=
    HornChildDiscovery.decodeParseAtom_arguments decoded
  have relation := HornChildDiscovery.decodeParseAtom_relation decoded
  have ground := HornChildDiscovery.decodeParseAtom_grammar_ground decoded
  have headEq : head =
      { relation := parseRelation
        arguments := Terms.ofList [parsed.grammar, input, value, output] } := by
    cases head with
    | mk headRelation headArguments =>
        simp only at relation arguments ⊢
        subst headRelation
        have actualArguments : headArguments =
            Terms.ofList [parsed.grammar, input, value, output] := by
          rw [← ofList_termsToList headArguments, arguments]
        subst headArguments
        rfl
  refine ⟨input, value, output, ?_⟩
  rw [semanticQuerySubstitution_apply_parserQuery substitution parseRelation
    parsed.grammar input value output ground]
  rw [semanticQuerySubstitution_apply_ruleAtom]
  rw [symbolicLPSubstitution_apply_encodeAtom substitution rule.head head
    instantiated]
  exact congrArg (encodeScopedAtom .query) headEq.symm

theorem instantiatedAtom_has_source_preimage
    (substitution : SymbolicSubstitution) (sources targets : List Atom)
    (instantiated : instantiateSymbolicAtoms substitution sources = some targets)
    {target : Atom} (member : target ∈ targets) :
    ∃ source ∈ sources,
      instantiateSymbolicAtom substitution source = some target := by
  induction sources generalizing targets with
  | nil =>
      simp [instantiateSymbolicAtoms] at instantiated
      subst targets
      simp at member
  | cons head tail inductionHypothesis =>
      rw [instantiateSymbolicAtoms, List.mapM_cons] at instantiated
      cases headResult : instantiateSymbolicAtom substitution head with
      | none => simp [headResult] at instantiated
      | some targetHead =>
          simp only [headResult] at instantiated
          cases tailResult : List.mapM (instantiateSymbolicAtom substitution) tail with
          | none => simp [tailResult] at instantiated
          | some targetTail =>
              simp [tailResult] at instantiated
              subst targets
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact ⟨head, by simp, headResult⟩
              · have tailInstantiated :
                    instantiateSymbolicAtoms substitution tail =
                      some targetTail := by
                    simpa [instantiateSymbolicAtoms] using tailResult
                obtain ⟨source, sourceMember, sourceResult⟩ :=
                  inductionHypothesis targetTail tailInstantiated member
                exact ⟨source, by simp [sourceMember], sourceResult⟩

theorem instantiateSymbolicTerms_preserves_length
    (substitution : SymbolicSubstitution) (source target : Terms)
    (instantiated : instantiateSymbolicTerms substitution source = some target) :
    (termsToList source).length = (termsToList target).length := by
  fun_induction termsToList source generalizing target with
  | case1 =>
      simp [instantiateSymbolicTerms] at instantiated
      subst target
      rfl
  | case2 head tail inductionHypothesis =>
      cases headResult : instantiateSymbolicTerm substitution head with
      | none => simp [instantiateSymbolicTerms, headResult] at instantiated
      | some targetHead =>
          cases tailResult : instantiateSymbolicTerms substitution tail with
          | none =>
              simp [instantiateSymbolicTerms, headResult, tailResult] at instantiated
          | some targetTail =>
              simp [instantiateSymbolicTerms, headResult, tailResult] at instantiated
              subst target
              simp [termsToList,
                inductionHypothesis targetTail tailResult]

theorem instantiateSymbolicAtom_preserves_relation
    {substitution : SymbolicSubstitution} {source target : Atom}
    (instantiated : instantiateSymbolicAtom substitution source = some target) :
    source.relation = target.relation := by
  unfold instantiateSymbolicAtom at instantiated
  cases result : instantiateSymbolicTerms substitution source.arguments with
  | none => simp [result] at instantiated
  | some arguments =>
      simp [result] at instantiated
      subst target
      rfl

theorem instantiateSymbolicAtom_source_arguments
    {substitution : SymbolicSubstitution} {source target : Atom}
    {targetGrammar targetInput targetValue targetOutput : Term}
    (instantiated : instantiateSymbolicAtom substitution source = some target)
    (targetArguments : termsToList target.arguments =
      [targetGrammar, targetInput, targetValue, targetOutput]) :
    ∃ sourceGrammar sourceInput sourceValue sourceOutput,
      termsToList source.arguments =
        [sourceGrammar, sourceInput, sourceValue, sourceOutput] := by
  unfold instantiateSymbolicAtom at instantiated
  cases result : instantiateSymbolicTerms substitution source.arguments with
  | none => simp [result] at instantiated
  | some arguments =>
      simp [result] at instantiated
      subst target
      have lengthEq := instantiateSymbolicTerms_preserves_length substitution
        source.arguments arguments result
      have sourceLength : (termsToList source.arguments).length = 4 := by
        rw [lengthEq]
        simpa using congrArg List.length targetArguments
      exact List.length_eq_four.mp sourceLength

theorem semanticQuerySubstitution_sourceChild
    {substitution : SymbolicSubstitution}
    {source target : Atom} {child sourceInput sourceValue sourceOutput : Term}
    {targetChild targetInput targetValue targetOutput : Term}
    (sourceArguments : termsToList source.arguments =
      [child, sourceInput, sourceValue, sourceOutput])
    (targetArguments : termsToList target.arguments =
      [targetChild, targetInput, targetValue, targetOutput])
    (instantiated : instantiateSymbolicAtom substitution source = some target)
    (queryInput queryValue queryOutput : Term) :
    (semanticQuerySubstitution substitution queryInput queryValue queryOutput).applyTerm
        (encodeScopedTerm .rule child) =
      encodeScopedTerm .query targetChild := by
  have sourceArgumentTerms : source.arguments =
      Terms.ofList [child, sourceInput, sourceValue, sourceOutput] := by
    rw [← ofList_termsToList source.arguments, sourceArguments]
  have targetArgumentTerms : target.arguments =
      Terms.ofList [targetChild, targetInput, targetValue, targetOutput] := by
    rw [← ofList_termsToList target.arguments, targetArguments]
  have atomEquality :
      (semanticQuerySubstitution substitution queryInput queryValue queryOutput).applyAtom
          (encodeScopedAtom .rule source) =
        encodeScopedAtom .query target := by
    rw [semanticQuerySubstitution_apply_ruleAtom]
    exact symbolicLPSubstitution_apply_encodeAtom substitution source target
      instantiated
  have argumentEquality := congrArg compilerAtomArguments atomEquality
  simp [compilerAtomArguments, Mettapedia.Logic.LP.Subst.applyAtom,
    encodeScopedAtom, sourceArgumentTerms, targetArgumentTerms] at argumentEquality
  exact (List.cons.inj argumentEquality).1

mutual
  theorem decodeCompilerTerm_encodeScopedTerm
      (origin : VariableOrigin) (source : Term) :
      decodeCompilerTerm (encodeScopedTerm origin source) = source := by
    cases source with
    | var identifier => simp [decodeCompilerTerm, encodeScopedTerm]
    | atom name => simp [decodeCompilerTerm, encodeScopedTerm]
    | integer value => simp [decodeCompilerTerm, encodeScopedTerm]
    | app constructor arguments =>
        simp only [encodeScopedTerm, decodeCompilerTerm]
        congr 1
        have listEq :
            (List.finRange (encodeScopedTerms origin arguments).length).map
                (fun index => decodeCompilerTerm
                  ((encodeScopedTerms origin arguments).get index)) =
              termsToList arguments := by
          rw [show (fun index => decodeCompilerTerm
              ((encodeScopedTerms origin arguments).get index)) =
            decodeCompilerTerm ∘ (encodeScopedTerms origin arguments).get by rfl]
          rw [← List.map_map, List.map_get_finRange]
          exact decodeCompilerTerms_encodeScopedTerms origin arguments
        exact (congrArg Terms.ofList listEq).trans
          (ofList_termsToList arguments)

  theorem decodeCompilerTerms_encodeScopedTerms
      (origin : VariableOrigin) (sources : Terms) :
      (encodeScopedTerms origin sources).map decodeCompilerTerm =
        termsToList sources := by
    cases sources with
    | nil => rfl
    | cons head tail =>
        simp only [encodeScopedTerms, List.map_cons, termsToList,
          List.cons.injEq]
        exact ⟨decodeCompilerTerm_encodeScopedTerm origin head,
          decodeCompilerTerms_encodeScopedTerms origin tail⟩
end

/-- Every recursive call in a certificate-independent semantic specialization
is represented by the child universe computed solely from admitted source
rules.  The finite unification bound exists for the admitted finite program;
range safety prevents the compiler MGU from dropping a residual child. -/
theorem semanticSpecialization_call_is_programChild
    {program : Program} {parseRelation : String} {rule : Rule}
    {substitution : SymbolicSubstitution} {categories : CategoryTable}
    {production : StreamProduction}
    (semantic : SemanticSpecializes program parseRelation rule substitution
      categories production)
    (programSafe : parserProgramSafe program parseRelation = true)
    {call : HornStream.ParseCall} (callMember : call ∈ production.calls) :
    ∃ parentGrammar maximumFuel childGrammar,
      childGrammar ∈
          programChildren program parseRelation maximumFuel parentGrammar ∧
        lookupCategory childGrammar categories = some call.category := by
  cases semantic with
  | intro head body parsedHead ruleMember substitutionValid categoriesValid
      instantiatedHead instantiatedBody decodedHead bodyEvidence sourceRule
      category start finish =>
    obtain ⟨targetAtom, targetMember, parsedChild, decodedChild, callEq⟩ :=
      Mettapedia.GSLT.Parsing.HornChildDiscovery.SemanticBodySpecializes.call_has_source_atom
        bodyEvidence callMember
    obtain ⟨sourceAtom, sourceMember, sourceInstantiated⟩ :=
      instantiatedAtom_has_source_preimage substitution rule.body body
        instantiatedBody targetMember
    obtain ⟨headInput, headValue, headOutput, headArguments⟩ :=
      HornChildDiscovery.decodeParseAtom_arguments decodedHead
    obtain ⟨childInput, childValue, childOutput, childArguments⟩ :=
      HornChildDiscovery.decodeParseAtom_arguments decodedChild
    have headRelation := HornChildDiscovery.decodeParseAtom_relation decodedHead
    have childRelation := HornChildDiscovery.decodeParseAtom_relation decodedChild
    have sourceChildRelation : sourceAtom.relation = parseRelation :=
      (instantiateSymbolicAtom_preserves_relation sourceInstantiated).trans
        childRelation
    obtain ⟨sourceHeadGrammar, sourceHeadInput, sourceHeadValue,
        sourceHeadOutput, sourceHeadArguments⟩ :=
      instantiateSymbolicAtom_source_arguments instantiatedHead headArguments
    have sourceHeadRelation : rule.head.relation = parseRelation :=
      (instantiateSymbolicAtom_preserves_relation instantiatedHead).trans
        headRelation
    obtain ⟨sourceChild, sourceInput, sourceValue, sourceOutput,
        sourceArguments⟩ : ∃ child input value output,
          termsToList sourceAtom.arguments = [child, input, value, output] := by
      have sourceSafe := parserProgramSafe_rule programSafe ruleMember
      have atomSafe := parserRuleSafe_body sourceHeadRelation sourceHeadArguments
        sourceSafe sourceMember
      unfold recursiveGrammarAtomSafe at atomSafe
      simp [sourceChildRelation] at atomSafe
      split at atomSafe <;> try contradiction
      next child input value output argumentsEq =>
        exact ⟨child, input, value, output, argumentsEq⟩
    obtain ⟨queryInput, queryValue, queryOutput, candidateUnifies⟩ :=
      semanticSpecializationHead_unifies_parserQuery instantiatedHead decodedHead
    obtain ⟨maximumFuel, bounded⟩ :=
      finiteProgram_has_unification_bound program
        (parserQuery parseRelation parsedHead.grammar)
    have semanticallyUnifiable :
        SemanticallyUnifiable
          (parserQuery parseRelation parsedHead.grammar) rule :=
      ⟨semanticQuerySubstitution substitution queryInput queryValue queryOutput,
        candidateUnifies⟩
    obtain ⟨headMatch, matchMember, matched⟩ :=
      matchHeads_semantically_exhaustive program
        (parserQuery parseRelation parsedHead.grammar) maximumFuel bounded rule
        ruleMember semanticallyUnifiable
    have sourceSafe := parserProgramSafe_rule programSafe ruleMember
    have parentGround := encodeScopedTerm_isGround_of_noVariables .query
      parsedHead.grammar
      (HornChildDiscovery.decodeParseAtom_grammar_ground decodedHead)
    have compilerMember := safeMatchedChild_mem_programChildren matchMember matched
      sourceHeadRelation sourceHeadArguments sourceSafe sourceMember
      sourceChildRelation sourceArguments parentGround
    have fixed := safeMatchedChild_fixed_under_unifier matched sourceHeadRelation
      sourceHeadArguments sourceSafe sourceMember sourceChildRelation sourceArguments
      parentGround
      (semanticQuerySubstitution substitution queryInput queryValue queryOutput)
      candidateUnifies
    have candidateChild := semanticQuerySubstitution_sourceChild sourceArguments
      childArguments sourceInstantiated queryInput queryValue queryOutput
    have decodedCompilerChild :
        decodeCompilerTerm
            (headMatch.substitution.applyTerm
              (encodeScopedTerm .rule sourceChild)) =
          parsedChild.grammar := by
      rw [← fixed, candidateChild, decodeCompilerTerm_encodeScopedTerm]
    have childMember : parsedChild.grammar ∈
        programChildren program parseRelation maximumFuel parsedHead.grammar := by
      simpa [decodedCompilerChild] using compilerMember
    subst call
    exact ⟨parsedHead.grammar, maximumFuel, parsedChild.grammar, childMember,
      HornChildDiscovery.decodeParseAtom_lookupCategory decodedChild⟩

/-- Fuel-free production reflection: every recursive call in a semantic
specialization occurs in the child universe computed by total unification from
the admitted source program.  Unlike the bounded compatibility theorem above,
this statement has no hidden search threshold whose exhaustion could be
mistaken for grammatical rejection. -/
theorem semanticSpecialization_call_is_programChildTotal
    {program : Program} {parseRelation : String} {rule : Rule}
    {substitution : SymbolicSubstitution} {categories : CategoryTable}
    {production : StreamProduction}
    (semantic : SemanticSpecializes program parseRelation rule substitution
      categories production)
    (programSafe : parserProgramSafe program parseRelation = true)
    {call : HornStream.ParseCall} (callMember : call ∈ production.calls) :
    ∃ parentGrammar childGrammar,
      childGrammar ∈
          programChildrenTotal program parseRelation parentGrammar ∧
        lookupCategory childGrammar categories = some call.category := by
  cases semantic with
  | intro head body parsedHead ruleMember substitutionValid categoriesValid
      instantiatedHead instantiatedBody decodedHead bodyEvidence sourceRule
      category start finish =>
    obtain ⟨targetAtom, targetMember, parsedChild, decodedChild, callEq⟩ :=
      Mettapedia.GSLT.Parsing.HornChildDiscovery.SemanticBodySpecializes.call_has_source_atom
        bodyEvidence callMember
    obtain ⟨sourceAtom, sourceMember, sourceInstantiated⟩ :=
      instantiatedAtom_has_source_preimage substitution rule.body body
        instantiatedBody targetMember
    obtain ⟨headInput, headValue, headOutput, headArguments⟩ :=
      HornChildDiscovery.decodeParseAtom_arguments decodedHead
    obtain ⟨childInput, childValue, childOutput, childArguments⟩ :=
      HornChildDiscovery.decodeParseAtom_arguments decodedChild
    have headRelation := HornChildDiscovery.decodeParseAtom_relation decodedHead
    have childRelation := HornChildDiscovery.decodeParseAtom_relation decodedChild
    have sourceChildRelation : sourceAtom.relation = parseRelation :=
      (instantiateSymbolicAtom_preserves_relation sourceInstantiated).trans
        childRelation
    obtain ⟨sourceHeadGrammar, sourceHeadInput, sourceHeadValue,
        sourceHeadOutput, sourceHeadArguments⟩ :=
      instantiateSymbolicAtom_source_arguments instantiatedHead headArguments
    have sourceHeadRelation : rule.head.relation = parseRelation :=
      (instantiateSymbolicAtom_preserves_relation instantiatedHead).trans
        headRelation
    obtain ⟨sourceChild, sourceInput, sourceValue, sourceOutput,
        sourceArguments⟩ : ∃ child input value output,
          termsToList sourceAtom.arguments = [child, input, value, output] := by
      have sourceSafe := parserProgramSafe_rule programSafe ruleMember
      have atomSafe := parserRuleSafe_body sourceHeadRelation sourceHeadArguments
        sourceSafe sourceMember
      unfold recursiveGrammarAtomSafe at atomSafe
      simp [sourceChildRelation] at atomSafe
      split at atomSafe <;> try contradiction
      next child input value output argumentsEq =>
        exact ⟨child, input, value, output, argumentsEq⟩
    obtain ⟨queryInput, queryValue, queryOutput, candidateUnifies⟩ :=
      semanticSpecializationHead_unifies_parserQuery instantiatedHead decodedHead
    have semanticallyUnifiable :
        SemanticallyUnifiable
          (parserQuery parseRelation parsedHead.grammar) rule :=
      ⟨semanticQuerySubstitution substitution queryInput queryValue queryOutput,
        candidateUnifies⟩
    obtain ⟨headMatch, matchMember, matched⟩ :=
      matchHeadsTotal_semantically_exhaustive program
        (parserQuery parseRelation parsedHead.grammar) rule ruleMember
        semanticallyUnifiable
    have sourceSafe := parserProgramSafe_rule programSafe ruleMember
    have parentGround := encodeScopedTerm_isGround_of_noVariables .query
      parsedHead.grammar
      (HornChildDiscovery.decodeParseAtom_grammar_ground decodedHead)
    have compilerMember := safeTotalMatchedChild_mem_programChildren matchMember
      matched sourceHeadRelation sourceHeadArguments sourceSafe sourceMember
      sourceChildRelation sourceArguments parentGround
    have fixed := safeTotalMatchedChild_fixed_under_unifier matched
      sourceHeadRelation sourceHeadArguments sourceSafe sourceMember
      sourceChildRelation sourceArguments parentGround
      (semanticQuerySubstitution substitution queryInput queryValue queryOutput)
      candidateUnifies
    have candidateChild := semanticQuerySubstitution_sourceChild sourceArguments
      childArguments sourceInstantiated queryInput queryValue queryOutput
    have decodedCompilerChild :
        decodeCompilerTerm
            (headMatch.substitution.applyTerm
              (encodeScopedTerm .rule sourceChild)) =
          parsedChild.grammar := by
      rw [← fixed, candidateChild, decodeCompilerTerm_encodeScopedTerm]
    have childMember : parsedChild.grammar ∈
        programChildrenTotal program parseRelation parsedHead.grammar := by
      simpa [decodedCompilerChild] using compilerMember
    subst call
    exact ⟨parsedHead.grammar, parsedChild.grammar, childMember,
      HornChildDiscovery.decodeParseAtom_lookupCategory decodedChild⟩

end Mettapedia.GSLT.Parsing.HornSemanticChildren
