import Mettapedia.GSLT.Parsing.HornRootUniverse
import Mettapedia.GSLT.Parsing.HornSpecializationBody

/-!
# Child-grammar discovery from admitted Horn bodies

Root closure must follow recursive parser calls found in instantiated Horn
rule bodies.  This module exposes their grammar arguments by ordinary relation
name, arity, and groundness checks.  It proves that every recursive call in
certificate-independent body semantics has a corresponding source atom and
therefore a structurally discovered child grammar.
-/

namespace Mettapedia.GSLT.Parsing.HornChildDiscovery

open HornCertificate HornSpecialization HornSpecializationBody HornRootUniverse

def childGrammar (parseRelation : String) (atom : Atom) : Option Term :=
  if atom.relation != parseRelation then none
  else
    match termsToList atom.arguments with
    | [grammar, _, _, _] =>
        if termVariables grammar != [] then none else some grammar
    | _ => none

def childGrammars (parseRelation : String) (atoms : List Atom) : List Term :=
  atoms.filterMap (childGrammar parseRelation)

def semanticChildren (parseRelation : String) (bodies : Term → List Atom)
    (grammar : Term) : List Term :=
  childGrammars parseRelation (bodies grammar)

theorem decodeParseAtom_childGrammar
    {parseRelation : String} {categories : CategoryTable}
    {atom : Atom} {parsed : ParsedAtom}
    (decoded : decodeParseAtom parseRelation categories atom = some parsed) :
    childGrammar parseRelation atom = some parsed.grammar := by
  by_cases mismatch : (atom.relation != parseRelation) = true
  · simp [decodeParseAtom, mismatch] at decoded
  · generalize argumentsEq : termsToList atom.arguments = arguments at decoded ⊢
    cases arguments with
    | nil => simp [decodeParseAtom, mismatch, argumentsEq] at decoded
    | cons grammar rest =>
        cases rest with
        | nil => simp [decodeParseAtom, mismatch, argumentsEq] at decoded
        | cons input rest =>
            cases rest with
            | nil => simp [decodeParseAtom, mismatch, argumentsEq] at decoded
            | cons value rest =>
                cases rest with
                | nil =>
                    simp [decodeParseAtom, mismatch, argumentsEq] at decoded
                | cons output rest =>
                    cases rest with
                    | cons extra rest =>
                        simp [decodeParseAtom, mismatch,
                          argumentsEq] at decoded
                    | nil =>
                        simp [decodeParseAtom, childGrammar, mismatch,
                          argumentsEq] at decoded ⊢
                        rcases decoded with ⟨ground, decoded⟩
                        refine ⟨ground, ?_⟩
                        cases categoryResult : lookupCategory grammar categories <;>
                          simp [categoryResult] at decoded
                        cases inputResult : decodeStream input <;>
                          simp [inputResult] at decoded
                        cases outputResult : decodeStream output <;>
                          simp [outputResult] at decoded
                        subst parsed
                        rfl

theorem decodeParseAtom_lookupCategory
    {parseRelation : String} {categories : CategoryTable}
    {atom : Atom} {parsed : ParsedAtom}
    (decoded : decodeParseAtom parseRelation categories atom = some parsed) :
    lookupCategory parsed.grammar categories = some parsed.category := by
  unfold decodeParseAtom at decoded
  split at decoded
  next relationMismatch => simp at decoded
  next relationMatch =>
    split at decoded <;> try contradiction
    next grammar input value output argumentsEq =>
      split at decoded
      next symbolic => simp at decoded
      next ground =>
        cases categoryResult : lookupCategory grammar categories <;>
          simp [categoryResult] at decoded
        cases inputResult : decodeStream input <;>
          simp [inputResult] at decoded
        cases outputResult : decodeStream output <;>
          simp [outputResult] at decoded
        subst parsed
        exact categoryResult

theorem decodeParseAtom_arguments
    {parseRelation : String} {categories : CategoryTable}
    {atom : Atom} {parsed : ParsedAtom}
    (decoded : decodeParseAtom parseRelation categories atom = some parsed) :
    ∃ input value output,
      termsToList atom.arguments = [parsed.grammar, input, value, output] := by
  unfold decodeParseAtom at decoded
  split at decoded
  next relationMismatch => simp at decoded
  next relationMatch =>
    split at decoded <;> try contradiction
    next grammar input value output argumentsEq =>
      split at decoded
      next symbolic => simp at decoded
      next ground =>
        cases categoryResult : lookupCategory grammar categories <;>
          simp [categoryResult] at decoded
        cases inputResult : decodeStream input <;>
          simp [inputResult] at decoded
        cases outputResult : decodeStream output <;>
          simp [outputResult] at decoded
        subst parsed
        exact ⟨input, value, output, argumentsEq⟩

theorem decodeParseAtom_relation
    {parseRelation : String} {categories : CategoryTable}
    {atom : Atom} {parsed : ParsedAtom}
    (decoded : decodeParseAtom parseRelation categories atom = some parsed) :
    atom.relation = parseRelation := by
  unfold decodeParseAtom at decoded
  split at decoded
  next relationMismatch => simp at decoded
  next relationMatch => simpa using relationMatch

theorem decodeParseAtom_grammar_ground
    {parseRelation : String} {categories : CategoryTable}
    {atom : Atom} {parsed : ParsedAtom}
    (decoded : decodeParseAtom parseRelation categories atom = some parsed) :
    termVariables parsed.grammar = [] := by
  unfold decodeParseAtom at decoded
  split at decoded
  next relationMismatch => simp at decoded
  next relationMatch =>
    split at decoded <;> try contradiction
    next grammar input value output argumentsEq =>
      split at decoded
      next symbolic => simp at decoded
      next ground =>
        cases categoryResult : lookupCategory grammar categories <;>
          simp [categoryResult] at decoded
        cases inputResult : decodeStream input <;>
          simp [inputResult] at decoded
        cases outputResult : decodeStream output <;>
          simp [outputResult] at decoded
        subst parsed
        simpa using ground

theorem decoded_childGrammar_mem
    {parseRelation : String} {categories : CategoryTable}
    {atoms : List Atom} {atom : Atom} {parsed : ParsedAtom}
    (member : atom ∈ atoms)
    (decoded : decodeParseAtom parseRelation categories atom = some parsed) :
    parsed.grammar ∈ childGrammars parseRelation atoms := by
  rw [childGrammars, List.mem_filterMap]
  exact ⟨atom, member, decodeParseAtom_childGrammar decoded⟩

theorem SemanticBodySpecializes.call_has_source_atom
    {program : Program} {parseRelation : String} {categories : CategoryTable}
    {atoms : List Atom} {calls : List HornStream.ParseCall}
    (semantic : SemanticBodySpecializes program parseRelation categories atoms calls)
    {call : HornStream.ParseCall} (member : call ∈ calls) :
    ∃ atom ∈ atoms, ∃ parsed,
      decodeParseAtom parseRelation categories atom = some parsed ∧
      call = parsed.toCall := by
  induction semantic with
  | nil => simp at member
  | parse atom atoms parsed calls relation decoded rest inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with equal | tailMember
      · exact ⟨atom, by simp, parsed, decoded, equal⟩
      · obtain ⟨source, sourceMember, sourceParsed, sourceDecoded, callEq⟩ :=
          inductionHypothesis tailMember
        exact ⟨source, List.mem_cons_of_mem _ sourceMember, sourceParsed,
          sourceDecoded, callEq⟩
  | side atom atoms goal fuel calls relation grounded derivation rest
      inductionHypothesis =>
      obtain ⟨source, sourceMember, sourceParsed, sourceDecoded, callEq⟩ :=
        inductionHypothesis member
      exact ⟨source, List.mem_cons_of_mem _ sourceMember, sourceParsed,
        sourceDecoded, callEq⟩

theorem SemanticBodySpecializes.call_has_discovered_grammar
    {program : Program} {parseRelation : String} {categories : CategoryTable}
    {atoms : List Atom} {calls : List HornStream.ParseCall}
    (semantic : SemanticBodySpecializes program parseRelation categories atoms calls)
    {call : HornStream.ParseCall} (member : call ∈ calls) :
    ∃ grammar ∈ childGrammars parseRelation atoms,
      ∃ atom ∈ atoms, ∃ parsed,
        decodeParseAtom parseRelation categories atom = some parsed ∧
        grammar = parsed.grammar ∧ call = parsed.toCall := by
  obtain ⟨atom, atomMember, parsed, decoded, callEq⟩ :=
    call_has_source_atom semantic member
  exact ⟨parsed.grammar,
    decoded_childGrammar_mem atomMember decoded,
    atom, atomMember, parsed, decoded, rfl, callEq⟩

theorem SemanticBodySpecializes.call_has_discovered_category
    {program : Program} {parseRelation : String} {categories : CategoryTable}
    {atoms : List Atom} {calls : List HornStream.ParseCall}
    (semantic : SemanticBodySpecializes program parseRelation categories atoms calls)
    {call : HornStream.ParseCall} (member : call ∈ calls) :
    ∃ grammar ∈ childGrammars parseRelation atoms,
      lookupCategory grammar categories = some call.category := by
  obtain ⟨atom, atomMember, parsed, decoded, callEq⟩ :=
    call_has_source_atom semantic member
  subst call
  exact ⟨parsed.grammar, decoded_childGrammar_mem atomMember decoded,
    decodeParseAtom_lookupCategory decoded⟩

theorem rootTable_covers_semantic_call
    {program : Program} {parseRelation : String} {root parent : Term}
    {bodies : Term → List Atom} {calls : List HornStream.ParseCall}
    {domain : List Term} {table : CategoryTable}
    (accepted : buildRootCategoryTable root
      (semanticChildren parseRelation bodies) domain = some table)
    (parentReachable : Reachable root (semanticChildren parseRelation bodies) parent)
    (semantic : SemanticBodySpecializes program parseRelation table
      (bodies parent) calls)
    {call : HornStream.ParseCall} (member : call ∈ calls) :
    ∃ grammar,
      Reachable root (semanticChildren parseRelation bodies) grammar ∧
      grammar ∈ domain ∧
      lookupCategory grammar table = some call.category := by
  obtain ⟨grammar, childMember, categoryFound⟩ :=
    Mettapedia.GSLT.Parsing.HornChildDiscovery.SemanticBodySpecializes.call_has_discovered_category
      semantic member
  have reachable : Reachable root (semanticChildren parseRelation bodies) grammar :=
    .child parentReachable childMember
  have domainMember := buildRootCategoryTable_lookup_is_in_universe
    accepted categoryFound
  exact ⟨grammar, reachable, domainMember, categoryFound⟩

/-! ## Executable controls -/

theorem classBody_discovers_no_recursive_grammar :
    childGrammars "parse"
      [{ relation := "member", arguments := Terms.ofList [.atom "digit", cp97] }] =
      [] := by
  decide

theorem parseAtom_discovers_its_ground_grammar :
    childGrammar "parse"
      { relation := "parse"
        arguments := Terms.ofList [HornCategoryTable.grammarA, .atom "nil",
          .atom "value", .atom "nil"] } =
      some HornCategoryTable.grammarA := by
  decide

theorem symbolicParseGrammar_is_rejected :
    childGrammar "parse"
      { relation := "parse"
        arguments := Terms.ofList [.var 0, .atom "nil", .atom "value",
          .atom "nil"] } = none := by
  decide

end Mettapedia.GSLT.Parsing.HornChildDiscovery
