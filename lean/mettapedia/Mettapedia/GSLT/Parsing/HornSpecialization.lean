import Mettapedia.GSLT.Parsing.HornCertificate
import Mettapedia.GSLT.Parsing.HornStream

/-!
# Checked specialization of admitted Horn parse rules

The packed parser does not interpret grammar constructors.  It specializes an
ordinary Horn relation at a ground grammar term, discharges non-recursive
premises with replayable Horn certificates, and recovers recursive stream
edges from the instantiated `parse/4` atoms.  This module is the independently
checked seam between the admitted Horn program and stream-path linearization.
-/

namespace Mettapedia.GSLT.Parsing.HornSpecialization

open CompilerCorrespondence HornCertificate HornStream

abbrev SymbolicSubstitution := List (Nat × Term)
abbrev CategoryTable := List (Term × Category)

def termsToList : Terms → List Term
  | .nil => []
  | .cons head tail => head :: termsToList tail

mutual
  def termVariables : Term → List Nat
    | .var identifier => [identifier]
    | .atom _ | .integer _ => []
    | .app _ arguments => termsVariables arguments

  def termsVariables : Terms → List Nat
    | .nil => []
    | .cons head tail => termVariables head ++ termsVariables tail
end

def atomVariables (atom : Atom) : List Nat :=
  termsVariables atom.arguments

def ruleVariables (rule : Rule) : List Nat :=
  (atomVariables rule.head ++ rule.body.flatMap atomVariables).eraseDups

def lookupSymbolic : Nat → SymbolicSubstitution → Option Term
  | _, [] => none
  | identifier, (candidate, value) :: rest =>
      if identifier = candidate then some value
      else lookupSymbolic identifier rest

mutual
  def instantiateSymbolicTerm
      (substitution : SymbolicSubstitution) : Term → Option Term
    | .var identifier => lookupSymbolic identifier substitution
    | .atom name => some (.atom name)
    | .integer value => some (.integer value)
    | .app constructor arguments => do
        let instantiated ← instantiateSymbolicTerms substitution arguments
        pure (.app constructor instantiated)

  def instantiateSymbolicTerms
      (substitution : SymbolicSubstitution) : Terms → Option Terms
    | .nil => some .nil
    | .cons head tail => do
        let instantiatedHead ← instantiateSymbolicTerm substitution head
        let instantiatedTail ← instantiateSymbolicTerms substitution tail
        pure (.cons instantiatedHead instantiatedTail)
end

def instantiateSymbolicAtom
    (substitution : SymbolicSubstitution) (atom : Atom) : Option Atom := do
  let arguments ← instantiateSymbolicTerms substitution atom.arguments
  pure { atom with arguments := arguments }

def instantiateSymbolicAtoms
    (substitution : SymbolicSubstitution) (atoms : List Atom) :
    Option (List Atom) :=
  atoms.mapM (instantiateSymbolicAtom substitution)

def symbolicSubstitutionValid
    (rule : Rule) (substitution : SymbolicSubstitution) : Bool :=
  decide substitution.unzip.1.Nodup &&
  substitution.unzip.1.all (ruleVariables rule).contains &&
  (ruleVariables rule).all substitution.unzip.1.contains &&
  substitution.all fun binding =>
    (termVariables binding.2).all fun identifier =>
      !(ruleVariables rule).contains identifier

def lookupCategory : Term → CategoryTable → Option Category
  | _, [] => none
  | grammar, (candidate, category) :: rest =>
      if grammar = candidate then some category else lookupCategory grammar rest

def categoryTableValid (categories : CategoryTable) : Bool :=
  decide (
    categories.unzip.1.Nodup ∧ categories.unzip.2.Nodup ∧
    ∀ entry ∈ categories, termVariables entry.1 = [])

mutual
  def termToGround : Term → Option GroundTerm
    | .var _ => none
    | .atom name => some (.atom name)
    | .integer value => some (.integer value)
    | .app constructor arguments => do
        let grounded ← termsToGround arguments
        pure (.app constructor grounded)

  def termsToGround : Terms → Option GroundTerms
    | .nil => some .nil
    | .cons head tail => do
        let groundedHead ← termToGround head
        let groundedTail ← termsToGround tail
        pure (.cons groundedHead groundedTail)
end

def atomToGround (atom : Atom) : Option GroundAtom := do
  let arguments ← termsToGround atom.arguments
  pure { relation := atom.relation, arguments := arguments }

def decodeCodepoint : Term → Option Codepoint
  | .app "cp" (.cons (.integer value) .nil) =>
      if value < 0 then none else some value.toNat
  | _ => none

def decodeStream : Term → Option StreamTerm
  | .var identifier => some (.var identifier)
  | .atom "nil" => some .nil
  | .app "cons" (.cons codepoint (.cons tail .nil)) => do
      let decodedTail ← decodeStream tail
      match codepoint with
      | .var _ => pure (.consAny decodedTail)
      | _ =>
          let decodedCodepoint ← decodeCodepoint codepoint
          pure (.consExact decodedCodepoint decodedTail)
  | _ => none

structure ParsedAtom where
  grammar : Term
  input : StreamTerm
  value : Term
  output : StreamTerm
  category : Category
  deriving DecidableEq, Repr

def decodeParseAtom
    (parseRelation : String) (categories : CategoryTable)
    (atom : Atom) : Option ParsedAtom := do
  if atom.relation != parseRelation then none else
  match termsToList atom.arguments with
  | [grammar, input, value, output] =>
      if termVariables grammar != [] then none else do
      let category ← lookupCategory grammar categories
      let decodedInput ← decodeStream input
      let decodedOutput ← decodeStream output
      pure {
        grammar := grammar
        input := decodedInput
        value := value
        output := decodedOutput
        category := category }
  | _ => none

def ParsedAtom.toCall (atom : ParsedAtom) : ParseCall :=
  { input := atom.input, output := atom.output, category := atom.category }

structure SideCertificate where
  fuel : Nat
  goal : GroundAtom
  certificate : HornCertificate.Certificate
  deriving DecidableEq, Repr

def decodeBody (program : Program) (parseRelation : String)
    (categories : CategoryTable) :
    List Atom → List SideCertificate → Option (List ParseCall)
  | [], [] => some []
  | [], _ :: _ => none
  | atom :: atoms, sides =>
      if atom.relation = parseRelation then do
        let parsed ← decodeParseAtom parseRelation categories atom
        let calls ← decodeBody program parseRelation categories atoms sides
        pure (parsed.toCall :: calls)
      else
        match sides with
        | [] => none
        | side :: remaining => do
            let goal ← atomToGround atom
            if goal != side.goal then none
            else if replay program side.fuel goal side.certificate != true then none
            else decodeBody program parseRelation categories atoms remaining

structure StreamProduction where
  sourceRule : RuleId
  category : Category
  start : StreamTerm
  finish : StreamTerm
  calls : List ParseCall
  deriving DecidableEq, Repr

structure SpecializationCertificate where
  rule : Rule
  substitution : SymbolicSubstitution
  categories : CategoryTable
  sides : List SideCertificate
  deriving DecidableEq, Repr

def specialize (program : Program) (parseRelation : String)
    (certificate : SpecializationCertificate) : Option StreamProduction := do
  if certificate.rule ∉ program then none
  else if symbolicSubstitutionValid certificate.rule certificate.substitution != true
    then none
  else if categoryTableValid certificate.categories != true then none
  else
    let head ← instantiateSymbolicAtom certificate.substitution certificate.rule.head
    let body ← instantiateSymbolicAtoms certificate.substitution certificate.rule.body
    let parsedHead ← decodeParseAtom parseRelation certificate.categories head
    let calls ← decodeBody program parseRelation certificate.categories body
      certificate.sides
    pure {
      sourceRule := certificate.rule.name
      category := parsedHead.category
      start := parsedHead.input
      finish := parsedHead.output
      calls := calls }

inductive BodySpecializes (program : Program) (parseRelation : String)
    (categories : CategoryTable) :
    List Atom → List SideCertificate → List ParseCall → Prop where
  | nil : BodySpecializes program parseRelation categories [] [] []
  | parse (atom : Atom) (atoms : List Atom) (sides : List SideCertificate)
      (parsed : ParsedAtom) (calls : List ParseCall)
      (relation : atom.relation = parseRelation)
      (decoded : decodeParseAtom parseRelation categories atom = some parsed)
      (rest : BodySpecializes program parseRelation categories atoms sides calls) :
      BodySpecializes program parseRelation categories (atom :: atoms) sides
        (parsed.toCall :: calls)
  | side (atom : Atom) (atoms : List Atom) (side : SideCertificate)
      (sides : List SideCertificate) (goal : GroundAtom)
      (calls : List ParseCall)
      (relation : atom.relation ≠ parseRelation)
      (grounded : atomToGround atom = some goal)
      (sameGoal : side.goal = goal)
      (replayed : replay program side.fuel goal side.certificate = true)
      (rest : BodySpecializes program parseRelation categories atoms sides calls) :
      BodySpecializes program parseRelation categories (atom :: atoms)
        (side :: sides) calls

theorem decodeBody_sound (program : Program) (parseRelation : String)
    (categories : CategoryTable) (atoms : List Atom)
    (sides : List SideCertificate) (calls : List ParseCall)
    (accepted : decodeBody program parseRelation categories atoms sides = some calls) :
    BodySpecializes program parseRelation categories atoms sides calls := by
  induction atoms generalizing sides calls with
  | nil =>
      cases sides with
      | nil =>
          simp [decodeBody] at accepted
          subst calls
          exact .nil
      | cons side sides => simp [decodeBody] at accepted
  | cons atom atoms inductionHypothesis =>
      by_cases relation : atom.relation = parseRelation
      · cases decoded : decodeParseAtom parseRelation categories atom with
        | none => simp [decodeBody, relation, decoded] at accepted
        | some parsed =>
            cases recursive : decodeBody program parseRelation categories atoms sides with
            | none => simp [decodeBody, relation, decoded, recursive] at accepted
            | some rest =>
                simp [decodeBody, relation, decoded, recursive] at accepted
                subst calls
                exact .parse atom atoms sides parsed rest relation decoded
                  (inductionHypothesis sides rest recursive)
      · cases sides with
        | nil => simp [decodeBody, relation] at accepted
        | cons side sides =>
            cases grounded : atomToGround atom with
            | none => simp [decodeBody, relation, grounded] at accepted
            | some goal =>
                by_cases sameGoal : goal = side.goal
                · have unpacked :
                      replay program side.fuel side.goal side.certificate = true ∧
                      decodeBody program parseRelation categories atoms sides =
                        some calls := by
                      simpa [decodeBody, relation, grounded, sameGoal] using accepted
                  have replayed :
                      replay program side.fuel goal side.certificate = true := by
                    simpa [sameGoal] using unpacked.1
                  exact .side atom atoms side sides goal calls relation grounded
                    sameGoal.symm replayed
                    (inductionHypothesis sides calls unpacked.2)
                · simp [decodeBody, relation, grounded, sameGoal] at accepted

theorem decodeBody_complete (program : Program) (parseRelation : String)
    (categories : CategoryTable) (atoms : List Atom)
    (sides : List SideCertificate) (calls : List ParseCall)
    (derivation :
      BodySpecializes program parseRelation categories atoms sides calls) :
    decodeBody program parseRelation categories atoms sides = some calls := by
  induction derivation with
  | nil => rfl
  | parse atom atoms sides parsed calls relation decoded _ inductionHypothesis =>
      simp [decodeBody, relation, decoded, inductionHypothesis]
  | side atom atoms side sides goal calls relation grounded sameGoal replayed
      _ inductionHypothesis =>
      simp [decodeBody, relation, grounded, sameGoal, replayed,
        inductionHypothesis]

theorem decodeBody_iff (program : Program) (parseRelation : String)
    (categories : CategoryTable) (atoms : List Atom)
    (sides : List SideCertificate) (calls : List ParseCall) :
    decodeBody program parseRelation categories atoms sides = some calls ↔
      BodySpecializes program parseRelation categories atoms sides calls :=
  ⟨decodeBody_sound program parseRelation categories atoms sides calls,
    decodeBody_complete program parseRelation categories atoms sides calls⟩

inductive Specializes (program : Program) (parseRelation : String)
    (certificate : SpecializationCertificate)
    (production : StreamProduction) : Prop where
  | intro (head : Atom) (body : List Atom) (parsedHead : ParsedAtom)
      (member : certificate.rule ∈ program)
      (substitutionValid :
        symbolicSubstitutionValid certificate.rule certificate.substitution = true)
      (categoriesValid : categoryTableValid certificate.categories = true)
      (instantiatedHead :
        instantiateSymbolicAtom certificate.substitution certificate.rule.head =
          some head)
      (instantiatedBody :
        instantiateSymbolicAtoms certificate.substitution certificate.rule.body =
          some body)
      (decodedHead :
        decodeParseAtom parseRelation certificate.categories head = some parsedHead)
      (bodyEvidence : BodySpecializes program parseRelation certificate.categories
        body certificate.sides production.calls)
      (sourceRule : production.sourceRule = certificate.rule.name)
      (category : production.category = parsedHead.category)
      (start : production.start = parsedHead.input)
      (finish : production.finish = parsedHead.output) :
      Specializes program parseRelation certificate production

theorem specialize_sound (program : Program) (parseRelation : String)
    (certificate : SpecializationCertificate) (production : StreamProduction)
    (accepted : specialize program parseRelation certificate = some production) :
    Specializes program parseRelation certificate production := by
  by_cases member : certificate.rule ∈ program
  · by_cases substitutionValid :
      symbolicSubstitutionValid certificate.rule certificate.substitution = true
    · by_cases categoriesValid : categoryTableValid certificate.categories = true
      · cases headEquation :
          instantiateSymbolicAtom certificate.substitution certificate.rule.head with
        | none => simp [specialize, member, substitutionValid, categoriesValid,
            headEquation] at accepted
        | some head =>
            cases bodyEquation :
                instantiateSymbolicAtoms certificate.substitution certificate.rule.body with
            | none => simp [specialize, member, substitutionValid, categoriesValid,
                headEquation, bodyEquation] at accepted
            | some body =>
                cases headDecoded :
                    decodeParseAtom parseRelation certificate.categories head with
                | none => simp [specialize, member, substitutionValid,
                    categoriesValid, headEquation, bodyEquation, headDecoded] at accepted
                | some parsedHead =>
                    cases bodyDecoded : decodeBody program parseRelation
                        certificate.categories body certificate.sides with
                    | none => simp [specialize, member, substitutionValid,
                        categoriesValid, headEquation, bodyEquation,
                        bodyDecoded] at accepted
                    | some calls =>
                        simp [specialize, member, substitutionValid,
                          categoriesValid, headEquation, bodyEquation,
                          headDecoded, bodyDecoded] at accepted
                        subst production
                        exact .intro head body parsedHead member substitutionValid
                          categoriesValid headEquation bodyEquation headDecoded
                          (decodeBody_sound program parseRelation
                            certificate.categories body certificate.sides calls bodyDecoded)
                          rfl rfl rfl rfl
      · simp [specialize, member, substitutionValid, categoriesValid] at accepted
    · simp [specialize, member, substitutionValid] at accepted
  · simp [specialize, member] at accepted

theorem specialize_complete (program : Program) (parseRelation : String)
    (certificate : SpecializationCertificate) (production : StreamProduction)
    (derivation : Specializes program parseRelation certificate production) :
    specialize program parseRelation certificate = some production := by
  cases derivation with
  | intro head body parsedHead member substitutionValid categoriesValid
      instantiatedHead instantiatedBody decodedHead bodyEvidence sourceRule
      category start finish =>
      have bodyDecoded := decodeBody_complete program parseRelation
        certificate.categories body certificate.sides production.calls bodyEvidence
      cases production
      cases parsedHead
      simp_all [specialize]

theorem specialize_iff (program : Program) (parseRelation : String)
    (certificate : SpecializationCertificate) (production : StreamProduction) :
    specialize program parseRelation certificate = some production ↔
      Specializes program parseRelation certificate production :=
  ⟨specialize_sound program parseRelation certificate production,
    specialize_complete program parseRelation certificate production⟩

def compileLinear (program : Program) (parseRelation : String)
    (certificate : SpecializationCertificate) (fuel : Nat) :
    Option (StreamProduction × List SourceSymbol) := do
  let production ← specialize program parseRelation certificate
  let symbols ← linearize fuel [] production.start production.finish production.calls
  pure (production, symbols)

structure LinearCompilation (program : Program) (parseRelation : String)
    (certificate : SpecializationCertificate)
    (production : StreamProduction) (symbols : List SourceSymbol) : Prop where
  specialization : Specializes program parseRelation certificate production
  streamPath : Linearizes [] production.start production.finish production.calls symbols

theorem compileLinear_sound (program : Program) (parseRelation : String)
    (certificate : SpecializationCertificate) (fuel : Nat)
    (production : StreamProduction) (symbols : List SourceSymbol)
    (accepted : compileLinear program parseRelation certificate fuel =
      some (production, symbols)) :
    LinearCompilation program parseRelation certificate production symbols := by
  cases specialization : specialize program parseRelation certificate with
  | none => simp [compileLinear, specialization] at accepted
  | some actualProduction =>
      cases path : linearize fuel [] actualProduction.start actualProduction.finish
          actualProduction.calls with
      | none => simp [compileLinear, specialization, path] at accepted
      | some actualSymbols =>
          simp [compileLinear, specialization, path] at accepted
          obtain ⟨rfl, rfl⟩ := accepted
          exact {
            specialization := specialize_sound program parseRelation certificate
              actualProduction specialization
            streamPath := linearize_sound fuel [] actualProduction.start
              actualProduction.finish actualProduction.calls actualSymbols path }

theorem compileLinear_complete (program : Program) (parseRelation : String)
    (certificate : SpecializationCertificate)
    (production : StreamProduction) (symbols : List SourceSymbol)
    (derivation :
      LinearCompilation program parseRelation certificate production symbols) :
    ∃ fuel, compileLinear program parseRelation certificate fuel =
      some (production, symbols) := by
  obtain ⟨specialization, streamPath⟩ := derivation
  have specialized := specialize_complete program parseRelation certificate
    production specialization
  obtain ⟨fuel, linearized⟩ := linearize_complete streamPath
  exact ⟨fuel, by simp [compileLinear, specialized, linearized]⟩

theorem compileLinear_iff (program : Program) (parseRelation : String)
    (certificate : SpecializationCertificate)
    (production : StreamProduction) (symbols : List SourceSymbol) :
    (∃ fuel, compileLinear program parseRelation certificate fuel =
      some (production, symbols)) ↔
      LinearCompilation program parseRelation certificate production symbols := by
  constructor
  · rintro ⟨fuel, accepted⟩
    exact compileLinear_sound program parseRelation certificate fuel production
      symbols accepted
  · exact compileLinear_complete program parseRelation certificate production symbols

/-! ## Executable positive and negative controls -/

def cp97 : Term := .app "cp" (Terms.ofList [.integer 97])
def char97 : Term := .app "char" (Terms.ofList [cp97])

def parseCharRule : Rule :=
  { name := "parse-char"
    head := {
      relation := "parse"
      arguments := Terms.ofList [
        .app "char" (Terms.ofList [.var 0]),
        .app "cons" (Terms.ofList [.var 0, .var 1]),
        .var 0,
        .var 1] }
    body := [] }

def memberDigitRule : Rule :=
  { name := "member-digit-97"
    head := { relation := "member", arguments := Terms.ofList [
      .atom "digit", cp97] }
    body := [] }

def parseClassRule : Rule :=
  { name := "parse-class"
    head := {
      relation := "parse"
      arguments := Terms.ofList [
        .app "class" (Terms.ofList [.var 0]),
        .app "cons" (Terms.ofList [.var 1, .var 2]),
        .var 1,
        .var 2] }
    body := [{ relation := "member", arguments := Terms.ofList [.var 0, .var 1] }] }

def exampleProgram : Program := [parseCharRule, parseClassRule, memberDigitRule]

def charCertificate : SpecializationCertificate :=
  { rule := parseCharRule
    substitution := [(0, cp97), (1, .var 10)]
    categories := [(char97, "g0")]
    sides := [] }

def charProduction : StreamProduction :=
  { sourceRule := "parse-char"
    category := "g0"
    start := .consExact 97 (.var 10)
    finish := .var 10
    calls := [] }

theorem charSpecialization_accepts :
    specialize exampleProgram "parse" charCertificate = some charProduction := by
  decide

theorem charLinearCompilation_accepts :
    compileLinear exampleProgram "parse" charCertificate 2 =
      some (charProduction, [.exact 97]) := by
  decide

theorem charLinearCompilation_isSound :
    LinearCompilation exampleProgram "parse" charCertificate charProduction
      [.exact 97] :=
  compileLinear_sound exampleProgram "parse" charCertificate 2 charProduction
    [.exact 97] charLinearCompilation_accepts

theorem charLinearCompilation_isComplete :
    ∃ fuel, compileLinear exampleProgram "parse" charCertificate fuel =
      some (charProduction, [.exact 97]) :=
  compileLinear_complete exampleProgram "parse" charCertificate charProduction
    [.exact 97] charLinearCompilation_isSound

theorem charLinearCompilation_checkedIff :
    (∃ fuel, compileLinear exampleProgram "parse" charCertificate fuel =
      some (charProduction, [.exact 97])) ↔
      LinearCompilation exampleProgram "parse" charCertificate charProduction
        [.exact 97] :=
  compileLinear_iff exampleProgram "parse" charCertificate charProduction
    [.exact 97]

def missingBindingCertificate : SpecializationCertificate :=
  { charCertificate with substitution := [(0, cp97)] }

theorem missingBinding_rejects :
    specialize exampleProgram "parse" missingBindingCertificate = none := by
  decide

def mutatedRuleCertificate : SpecializationCertificate :=
  { charCertificate with rule := { parseCharRule with name := "not-admitted" } }

theorem mutatedRule_rejects :
    specialize exampleProgram "parse" mutatedRuleCertificate = none := by
  decide

theorem mutatedRule_notSpecialized :
    ¬ Specializes exampleProgram "parse" mutatedRuleCertificate charProduction := by
  intro claimed
  have accepted := specialize_complete exampleProgram "parse"
    mutatedRuleCertificate charProduction claimed
  rw [mutatedRule_rejects] at accepted
  contradiction

def digitGoal : GroundAtom :=
  { relation := "member"
    arguments := GroundTerms.ofList [
      .atom "digit", .app "cp" (GroundTerms.ofList [.integer 97])] }

def digitProof : HornCertificate.Certificate :=
  .node memberDigitRule [] .nil

def classCertificate : SpecializationCertificate :=
  { rule := parseClassRule
    substitution := [
      (0, .atom "digit"),
      (1, cp97),
      (2, .var 10)]
    categories := [(.app "class" (Terms.ofList [.atom "digit"]), "g0")]
    sides := [{ fuel := 1, goal := digitGoal, certificate := digitProof }] }

def classProduction : StreamProduction :=
  { sourceRule := "parse-class"
    category := "g0"
    start := .consExact 97 (.var 10)
    finish := .var 10
    calls := [] }

theorem classSidePremise_accepts :
    compileLinear exampleProgram "parse" classCertificate 2 =
      some (classProduction, [.exact 97]) := by
  decide

def wrongSideCertificate : SpecializationCertificate :=
  { classCertificate with sides := [
      { fuel := 1
        goal := { digitGoal with relation := "not-member" }
        certificate := digitProof }] }

theorem wrongSidePremise_rejects :
    specialize exampleProgram "parse" wrongSideCertificate = none := by
  decide

end Mettapedia.GSLT.Parsing.HornSpecialization
