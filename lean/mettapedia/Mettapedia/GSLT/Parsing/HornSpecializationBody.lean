import Mettapedia.GSLT.Parsing.HornSpecializationHead

/-!
# Semantic authority for specialization side premises

Non-parse premises used while specializing a syntax-GSLT rule are accepted
only with replayable Horn certificates.  This module projects the operational
body checker to the bounded Horn derivability relation, so an accepted
specialization cannot smuggle an engine-only side condition into the compiled
grammar.
-/

namespace Mettapedia.GSLT.Parsing.HornSpecializationBody

open HornCertificate HornSpecialization
open CompilerCorrespondence

theorem BodySpecializes.side_replays
    {program : Program} {parseRelation : String} {categories : CategoryTable}
    {atoms : List Atom} {sides : List SideCertificate}
    {calls : List HornStream.ParseCall}
    (specializes : BodySpecializes program parseRelation categories atoms sides calls)
    (side : SideCertificate) (member : side ∈ sides) :
    replay program side.fuel side.goal side.certificate = true := by
  induction specializes with
  | nil => simp at member
  | parse atom atoms sides parsed calls relation decoded rest inductionHypothesis =>
      exact inductionHypothesis member
  | side atom atoms headSide sides goal calls relation grounded sameGoal replayed
      rest inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with rfl | tailMember
      · simpa [sameGoal] using replayed
      · exact inductionHypothesis tailMember

theorem BodySpecializes.side_derives
    {program : Program} {parseRelation : String} {categories : CategoryTable}
    {atoms : List Atom} {sides : List SideCertificate}
    {calls : List HornStream.ParseCall}
    (specializes : BodySpecializes program parseRelation categories atoms sides calls)
    (side : SideCertificate) (member : side ∈ sides) :
    DerivesWithin program side.fuel side.goal :=
  replay_sound program side.fuel side.goal side.certificate
    (side_replays specializes side member)

theorem Specializes.every_side_derives
    {program : Program} {parseRelation : String}
    {certificate : SpecializationCertificate} {production : StreamProduction}
    (specializes : Specializes program parseRelation certificate production) :
    ∀ side ∈ certificate.sides,
      DerivesWithin program side.fuel side.goal := by
  cases specializes with
  | intro head body parsedHead member substitutionValid categoriesValid
      instantiatedHead instantiatedBody decodedHead bodyEvidence sourceRule
      category start finish =>
      intro side sideMember
      exact BodySpecializes.side_derives bodyEvidence side sideMember

/-- Bounded semantic derivability is sufficient to produce the proof object
required by a specialization side premise. -/
theorem sideCertificate_exists_of_derives
    {program : Program} {fuel : Nat} {goal : GroundAtom}
    (derivation : DerivesWithin program fuel goal) :
    ∃ side : SideCertificate,
      side.fuel = fuel ∧ side.goal = goal ∧
        replay program side.fuel side.goal side.certificate = true := by
  obtain ⟨certificate, accepted⟩ :=
    derivesWithin_complete program fuel goal derivation
  exact ⟨{ fuel, goal, certificate }, rfl, rfl, accepted⟩

/-! ## Certificate-independent body semantics

`SemanticBodySpecializes` states the meaning of an instantiated rule body
without mentioning certificate syntax.  Parse premises decode to recursive
stream calls; every other premise must be derivable from the admitted Horn
program.  The two correspondence theorems below show that replayable side
certificates are exactly evidence for this relation, rather than an extra
source of parsing semantics.
-/

inductive SemanticBodySpecializes (program : Program) (parseRelation : String)
    (categories : CategoryTable) : List Atom → List HornStream.ParseCall → Prop where
  | nil : SemanticBodySpecializes program parseRelation categories [] []
  | parse (atom : Atom) (atoms : List Atom) (parsed : ParsedAtom)
      (calls : List HornStream.ParseCall)
      (relation : atom.relation = parseRelation)
      (decoded : decodeParseAtom parseRelation categories atom = some parsed)
      (rest : SemanticBodySpecializes program parseRelation categories atoms calls) :
      SemanticBodySpecializes program parseRelation categories (atom :: atoms)
        (parsed.toCall :: calls)
  | side (atom : Atom) (atoms : List Atom) (goal : GroundAtom) (fuel : Nat)
      (calls : List HornStream.ParseCall)
      (relation : atom.relation ≠ parseRelation)
      (grounded : atomToGround atom = some goal)
      (derivation : DerivesWithin program fuel goal)
      (rest : SemanticBodySpecializes program parseRelation categories atoms calls) :
      SemanticBodySpecializes program parseRelation categories (atom :: atoms) calls

theorem BodySpecializes.toSemantic
    {program : Program} {parseRelation : String} {categories : CategoryTable}
    {atoms : List Atom} {sides : List SideCertificate}
    {calls : List HornStream.ParseCall}
    (specializes : BodySpecializes program parseRelation categories atoms sides calls) :
    SemanticBodySpecializes program parseRelation categories atoms calls := by
  induction specializes with
  | nil => exact .nil
  | parse atom atoms sides parsed calls relation decoded rest inductionHypothesis =>
      exact .parse atom atoms parsed calls relation decoded inductionHypothesis
  | side atom atoms side sides goal calls relation grounded sameGoal replayed
      rest inductionHypothesis =>
      exact .side atom atoms goal side.fuel calls relation grounded
        (replay_sound program side.fuel goal side.certificate replayed)
        inductionHypothesis

theorem SemanticBodySpecializes.hasCertificates
    {program : Program} {parseRelation : String} {categories : CategoryTable}
    {atoms : List Atom} {calls : List HornStream.ParseCall}
    (semantic : SemanticBodySpecializes program parseRelation categories atoms calls) :
    ∃ sides : List SideCertificate,
      BodySpecializes program parseRelation categories atoms sides calls := by
  induction semantic with
  | nil => exact ⟨[], .nil⟩
  | parse atom atoms parsed calls relation decoded rest inductionHypothesis =>
      obtain ⟨sides, certifiedRest⟩ := inductionHypothesis
      exact ⟨sides,
        .parse atom atoms sides parsed calls relation decoded certifiedRest⟩
  | side atom atoms goal fuel calls relation grounded derivation rest
      inductionHypothesis =>
      obtain ⟨certificate, replayed⟩ :=
        derivesWithin_complete program fuel goal derivation
      obtain ⟨sides, certifiedRest⟩ := inductionHypothesis
      let side : SideCertificate := { fuel, goal, certificate }
      exact ⟨side :: sides,
        .side atom atoms side sides goal calls relation grounded rfl replayed
          certifiedRest⟩

theorem semanticBodySpecializes_iff_exists_certificates
    (program : Program) (parseRelation : String) (categories : CategoryTable)
    (atoms : List Atom) (calls : List HornStream.ParseCall) :
    SemanticBodySpecializes program parseRelation categories atoms calls ↔
      ∃ sides : List SideCertificate,
        BodySpecializes program parseRelation categories atoms sides calls := by
  constructor
  · exact SemanticBodySpecializes.hasCertificates
  · rintro ⟨sides, specializes⟩
    exact
      Mettapedia.GSLT.Parsing.HornSpecializationBody.BodySpecializes.toSemantic
        specializes

inductive SemanticSpecializes (program : Program) (parseRelation : String)
    (rule : Rule) (substitution : SymbolicSubstitution)
    (categories : CategoryTable) (production : StreamProduction) : Prop where
  | intro (head : Atom) (body : List Atom) (parsedHead : ParsedAtom)
      (member : rule ∈ program)
      (substitutionValid : symbolicSubstitutionValid rule substitution = true)
      (categoriesValid : categoryTableValid categories = true)
      (instantiatedHead : instantiateSymbolicAtom substitution rule.head = some head)
      (instantiatedBody : instantiateSymbolicAtoms substitution rule.body = some body)
      (decodedHead : decodeParseAtom parseRelation categories head = some parsedHead)
      (bodyEvidence :
        SemanticBodySpecializes program parseRelation categories body production.calls)
      (sourceRule : production.sourceRule = rule.name)
      (category : production.category = parsedHead.category)
      (start : production.start = parsedHead.input)
      (finish : production.finish = parsedHead.output) :
      SemanticSpecializes program parseRelation rule substitution categories production

theorem Specializes.toSemantic
    {program : Program} {parseRelation : String}
    {certificate : SpecializationCertificate} {production : StreamProduction}
    (specializes : Specializes program parseRelation certificate production) :
    SemanticSpecializes program parseRelation certificate.rule
      certificate.substitution certificate.categories production := by
  cases specializes with
  | intro head body parsedHead member substitutionValid categoriesValid
      instantiatedHead instantiatedBody decodedHead bodyEvidence sourceRule
      category start finish =>
      exact .intro head body parsedHead member substitutionValid categoriesValid
        instantiatedHead instantiatedBody decodedHead
        (Mettapedia.GSLT.Parsing.HornSpecializationBody.BodySpecializes.toSemantic
          bodyEvidence)
        sourceRule category start finish

theorem SemanticSpecializes.hasCertificate
    {program : Program} {parseRelation : String} {rule : Rule}
    {substitution : SymbolicSubstitution} {categories : CategoryTable}
    {production : StreamProduction}
    (semantic : SemanticSpecializes program parseRelation rule substitution
      categories production) :
    ∃ sides : List SideCertificate,
      Specializes program parseRelation
        { rule := rule, substitution := substitution, categories := categories,
          sides := sides }
        production := by
  cases semantic with
  | intro head body parsedHead member substitutionValid categoriesValid
      instantiatedHead instantiatedBody decodedHead bodyEvidence sourceRule
      category start finish =>
      obtain ⟨sides, certifiedBody⟩ := bodyEvidence.hasCertificates
      exact ⟨sides, .intro head body parsedHead member substitutionValid
        categoriesValid instantiatedHead instantiatedBody decodedHead
        certifiedBody sourceRule category start finish⟩

theorem semanticSpecializes_iff_exists_certificate
    (program : Program) (parseRelation : String) (rule : Rule)
    (substitution : SymbolicSubstitution) (categories : CategoryTable)
    (production : StreamProduction) :
    SemanticSpecializes program parseRelation rule substitution categories production ↔
      ∃ sides : List SideCertificate,
        Specializes program parseRelation
          { rule := rule, substitution := substitution, categories := categories,
            sides := sides }
          production := by
  constructor
  · exact SemanticSpecializes.hasCertificate
  · rintro ⟨sides, specializes⟩
    exact
      Mettapedia.GSLT.Parsing.HornSpecializationBody.Specializes.toSemantic
        specializes

structure SemanticLinearCompilation (program : Program) (parseRelation : String)
    (rule : Rule) (substitution : SymbolicSubstitution)
    (categories : CategoryTable) (production : StreamProduction)
    (symbols : List SourceSymbol) : Prop where
  specialization :
    SemanticSpecializes program parseRelation rule substitution categories production
  streamPath :
    HornStream.Linearizes [] production.start production.finish production.calls symbols

theorem semanticLinearCompilation_iff_exists_certificate
    (program : Program) (parseRelation : String) (rule : Rule)
    (substitution : SymbolicSubstitution) (categories : CategoryTable)
    (production : StreamProduction) (symbols : List SourceSymbol) :
    SemanticLinearCompilation program parseRelation rule substitution categories
        production symbols ↔
      ∃ sides : List SideCertificate, ∃ fuel,
        compileLinear program parseRelation
          { rule := rule, substitution := substitution, categories := categories,
            sides := sides }
          fuel = some (production, symbols) := by
  constructor
  · intro semantic
    obtain ⟨sides, specialization⟩ := semantic.specialization.hasCertificate
    obtain ⟨fuel, accepted⟩ := compileLinear_complete program parseRelation
      { rule := rule, substitution := substitution, categories := categories,
        sides := sides }
      production symbols
      { specialization := specialization, streamPath := semantic.streamPath }
    exact ⟨sides, fuel, accepted⟩
  · rintro ⟨sides, fuel, accepted⟩
    have compiled := compileLinear_sound program parseRelation
      { rule := rule, substitution := substitution, categories := categories,
        sides := sides }
      fuel production symbols accepted
    exact {
      specialization :=
        Mettapedia.GSLT.Parsing.HornSpecializationBody.Specializes.toSemantic
          compiled.specialization
      streamPath := compiled.streamPath }

theorem classBody_has_certificate_independent_semantics :
    SemanticBodySpecializes exampleProgram "parse"
      classCertificate.categories
      [{ relation := "member"
         arguments := Terms.ofList [.atom "digit", cp97] }]
      [] := by
  apply SemanticBodySpecializes.side _ _ digitGoal 1 []
  · decide
  · decide
  · exact replay_sound exampleProgram 1 digitGoal digitProof (by decide)
  · exact .nil

theorem classRule_has_certificate_independent_semantics :
    SemanticSpecializes exampleProgram "parse" classCertificate.rule
      classCertificate.substitution classCertificate.categories classProduction := by
  exact
    Mettapedia.GSLT.Parsing.HornSpecializationBody.Specializes.toSemantic
      (specialize_sound exampleProgram "parse" classCertificate classProduction
        (by decide))

theorem classRule_has_certificate_independent_linear_compilation :
    SemanticLinearCompilation exampleProgram "parse" classCertificate.rule
      classCertificate.substitution classCertificate.categories classProduction
      [.exact 97] := by
  rw [semanticLinearCompilation_iff_exists_certificate]
  exact ⟨classCertificate.sides, 2, classSidePremise_accepts⟩

theorem mutatedRule_has_no_semantic_specialization :
    ¬ SemanticSpecializes exampleProgram "parse" mutatedRuleCertificate.rule
      mutatedRuleCertificate.substitution mutatedRuleCertificate.categories
      charProduction := by
  intro semantic
  cases semantic with
  | intro head body parsedHead member substitutionValid categoriesValid
      instantiatedHead instantiatedBody decodedHead bodyEvidence sourceRule
      category start finish =>
      have absent : mutatedRuleCertificate.rule ∉ exampleProgram := by decide
      exact absent member

theorem mutatedRule_has_no_semantic_linear_compilation
    (symbols : List SourceSymbol) :
    ¬ SemanticLinearCompilation exampleProgram "parse"
      mutatedRuleCertificate.rule mutatedRuleCertificate.substitution
      mutatedRuleCertificate.categories charProduction symbols := by
  intro semantic
  exact mutatedRule_has_no_semantic_specialization semantic.specialization

theorem emptyProgram_derives_none {fuel : Nat} {goal : GroundAtom} :
    ¬ DerivesWithin [] fuel goal := by
  intro derivation
  cases derivation with
  | apply fuel goal rule member substitution valid goals head body premises =>
      simp at member

def unknownSideAtom : Atom :=
  { relation := "unknown-side", arguments := .nil }

theorem unknownBody_has_no_semantics :
    ¬ SemanticBodySpecializes [] "parse" [] [unknownSideAtom] [] := by
  intro semantic
  cases semantic with
  | side atom atoms goal fuel calls relation grounded derivation rest =>
      exact emptyProgram_derives_none derivation

end Mettapedia.GSLT.Parsing.HornSpecializationBody
