import Mettapedia.GSLT.Parsing.HornUnification
import Mettapedia.GSLT.Parsing.HornSpecialization

/-!
# Admission of structurally total Horn side rules

Non-parse premises used during parser specialization must not inherit an
unbounded host search policy.  This module recognizes a generic query-directed
fragment: ground facts and range-safe recursive rules whose arguments never
grow and at least one argument is a strict syntactic subterm.  The check is
independent of guest-language names and parser constructors.
-/

namespace Mettapedia.GSLT.Parsing.HornSideAdmission

open HornCertificate HornSpecialization HornUnification

def termIsSubtermFuel : Nat → Term → Term → Bool
  | 0, _, _ => false
  | fuel + 1, candidate, source =>
      decide (candidate = source) ||
        match source with
        | .app _ arguments =>
            (termsToList arguments).any (termIsSubtermFuel fuel candidate)
        | .var _ | .atom _ | .integer _ => false

def termIsSubterm (candidate source : Term) : Bool :=
  termIsSubtermFuel (encodeScopedTerm .rule source).size candidate source

def termIsStrictSubterm (candidate source : Term) : Bool :=
  decide (candidate ≠ source) && termIsSubterm candidate source

theorem encodeScopedTerm_mem_encodeScopedTerms
    {origin : VariableOrigin} {candidate : Term} {sources : Terms}
    (member : candidate ∈ termsToList sources) :
    encodeScopedTerm origin candidate ∈ encodeScopedTerms origin sources := by
  fun_induction termsToList sources
  next => simp at member
  next head tail inductionHypothesis =>
    simp only [List.mem_cons] at member
    simp only [encodeScopedTerms, List.mem_cons]
    rcases member with rfl | tailMember
    · exact Or.inl rfl
    · exact Or.inr (inductionHypothesis tailMember)

theorem applyTerm_size_le_of_termIsSubtermFuel
    (substitution : Mettapedia.Logic.LP.Subst compilerSignature)
    (fuel : Nat) (candidate source : Term)
    (accepted : termIsSubtermFuel fuel candidate source = true) :
    (substitution.applyTerm (encodeScopedTerm .rule candidate)).size ≤
      (substitution.applyTerm (encodeScopedTerm .rule source)).size := by
  induction fuel generalizing source with
  | zero => simp [termIsSubtermFuel] at accepted
  | succ fuel inductionHypothesis =>
      simp only [termIsSubtermFuel, Bool.or_eq_true, decide_eq_true_eq] at accepted
      rcases accepted with equal | nested
      · subst source
        exact Nat.le_refl _
      · cases source with
        | var identifier => simp at nested
        | atom name => simp at nested
        | integer value => simp at nested
        | app constructor arguments =>
            obtain ⟨child, childMember, childAccepted⟩ :=
              List.any_eq_true.mp nested
            have encodedMember :
                encodeScopedTerm .rule child ∈
                  encodeScopedTerms .rule arguments :=
              encodeScopedTerm_mem_encodeScopedTerms childMember
            rw [List.mem_iff_get] at encodedMember
            obtain ⟨index, encodedAt⟩ := encodedMember
            have candidateLeChild :=
              inductionHypothesis child childAccepted
            have childLtSource :
                (substitution.applyTerm
                    (encodeScopedTerm .rule child)).size <
                  (substitution.applyTerm
                    (encodeScopedTerm .rule
                      (.app constructor arguments))).size := by
              have direct := Mettapedia.Logic.LP.Term.size_subterm
                (f := ({ name := constructor, arity :=
                  (encodeScopedTerms .rule arguments).length } :
                    FunctionSymbol))
                (ts := fun position =>
                  substitution.applyTerm
                    ((encodeScopedTerms .rule arguments).get position))
                index
              rw [← encodedAt]
              simpa [encodeScopedTerm,
                Mettapedia.Logic.LP.Subst.applyTerm] using direct
            omega

theorem applyTerm_size_lt_of_termIsStrictSubterm
    (substitution : Mettapedia.Logic.LP.Subst compilerSignature)
    (candidate source : Term)
    (accepted : termIsStrictSubterm candidate source = true) :
    (substitution.applyTerm (encodeScopedTerm .rule candidate)).size <
      (substitution.applyTerm (encodeScopedTerm .rule source)).size := by
  simp only [termIsStrictSubterm, Bool.and_eq_true,
    decide_eq_true_eq] at accepted
  obtain ⟨notEqual, subterm⟩ := accepted
  unfold termIsSubterm at subterm
  -- A strict accepted subterm must occur beneath an application node.  The
  -- fuel theorem supplies non-strict preservation; the outer application
  -- supplies the strict step.
  have sizePositive :
      0 < (encodeScopedTerm .rule source).size :=
    Mettapedia.Logic.LP.Term.size_pos _
  obtain ⟨fuel, sizeEqual⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt sizePositive)
  rw [sizeEqual] at subterm
  simp only [termIsSubtermFuel, Bool.or_eq_true,
    decide_eq_true_eq] at subterm
  rcases subterm with equal | nested
  · exact (notEqual equal).elim
  · cases source with
    | var identifier => simp at nested
    | atom name => simp at nested
    | integer value => simp at nested
    | app constructor arguments =>
        obtain ⟨child, childMember, childAccepted⟩ :=
          List.any_eq_true.mp nested
        have encodedMember :
            encodeScopedTerm .rule child ∈
              encodeScopedTerms .rule arguments :=
          encodeScopedTerm_mem_encodeScopedTerms childMember
        rw [List.mem_iff_get] at encodedMember
        obtain ⟨index, encodedAt⟩ := encodedMember
        have candidateLeChild := applyTerm_size_le_of_termIsSubtermFuel
          substitution _ candidate child childAccepted
        have childLtSource :
            (substitution.applyTerm (encodeScopedTerm .rule child)).size <
              (substitution.applyTerm
                (encodeScopedTerm .rule (.app constructor arguments))).size := by
          have direct := Mettapedia.Logic.LP.Term.size_subterm
            (f := ({ name := constructor, arity :=
              (encodeScopedTerms .rule arguments).length } :
                FunctionSymbol))
            (ts := fun position => substitution.applyTerm
              ((encodeScopedTerms .rule arguments).get position))
            index
          rw [← encodedAt]
          simpa [encodeScopedTerm,
            Mettapedia.Logic.LP.Subst.applyTerm] using direct
        omega

def variablesContained (source target : List Nat) : Bool :=
  source.all target.contains

def premiseStructurallyDecreases (head premise : Atom) : Bool :=
  let headArguments := termsToList head.arguments
  let premiseArguments := termsToList premise.arguments
  decide (premise.relation = head.relation) &&
  decide (premiseArguments.length = headArguments.length) &&
  variablesContained (atomVariables premise) (atomVariables head) &&
  ((headArguments.zip premiseArguments).all fun pair =>
    termIsSubterm pair.2 pair.1) &&
  (headArguments.zip premiseArguments).any fun pair =>
    termIsStrictSubterm pair.2 pair.1

theorem premiseStructurallyDecreases_components
    {head premise : Atom}
    (accepted : premiseStructurallyDecreases head premise = true) :
    premise.relation = head.relation ∧
      (termsToList premise.arguments).length =
        (termsToList head.arguments).length ∧
      variablesContained (atomVariables premise) (atomVariables head) = true ∧
      ((termsToList head.arguments).zip
        (termsToList premise.arguments)).all
          (fun pair => termIsSubterm pair.2 pair.1) = true ∧
      ((termsToList head.arguments).zip
        (termsToList premise.arguments)).any
          (fun pair => termIsStrictSubterm pair.2 pair.1) = true := by
  simpa [premiseStructurallyDecreases, Bool.and_eq_true, and_assoc] using accepted

def termMeasure
    (substitution : Mettapedia.Logic.LP.Subst compilerSignature)
    (term : Term) : Nat :=
  (substitution.applyTerm (encodeScopedTerm .rule term)).size

def atomMeasure
    (substitution : Mettapedia.Logic.LP.Subst compilerSignature)
    (atom : Atom) : Nat :=
  ((termsToList atom.arguments).map (termMeasure substitution)).sum

theorem atomMeasure_lt_of_premiseStructurallyDecreases
    (substitution : Mettapedia.Logic.LP.Subst compilerSignature)
    {head premise : Atom}
    (accepted : premiseStructurallyDecreases head premise = true) :
    atomMeasure substitution premise < atomMeasure substitution head := by
  obtain ⟨relation, lengths, variableCheck, allSubterms, oneStrict⟩ :=
    premiseStructurallyDecreases_components accepted
  let pairs := (termsToList head.arguments).zip
    (termsToList premise.arguments)
  have everyLe : ∀ pair ∈ pairs,
      termMeasure substitution pair.2 ≤ termMeasure substitution pair.1 := by
    intro pair member
    have acceptedPair := (List.all_eq_true.mp allSubterms) pair member
    exact applyTerm_size_le_of_termIsSubtermFuel substitution _ pair.2 pair.1
      (by simpa [termIsSubterm] using acceptedPair)
  have oneLt : ∃ pair ∈ pairs,
      termMeasure substitution pair.2 < termMeasure substitution pair.1 := by
    obtain ⟨pair, member, strict⟩ := List.any_eq_true.mp oneStrict
    exact ⟨pair, member,
      applyTerm_size_lt_of_termIsStrictSubterm substitution pair.2 pair.1 strict⟩
  have sumsLt := List.sum_lt_sum
    (fun pair : Term × Term => termMeasure substitution pair.2)
    (fun pair : Term × Term => termMeasure substitution pair.1)
    everyLe oneLt
  have headLengthLe :
      (termsToList head.arguments).length ≤
        (termsToList premise.arguments).length := by omega
  have premiseLengthLe :
      (termsToList premise.arguments).length ≤
        (termsToList head.arguments).length := by omega
  have firsts := List.map_fst_zip headLengthLe
  have seconds := List.map_snd_zip premiseLengthLe
  unfold atomMeasure
  calc
    ((termsToList premise.arguments).map
      (termMeasure substitution)).sum =
        (((pairs.map Prod.snd).map
          (termMeasure substitution)).sum) := by rw [seconds]
    _ = (pairs.map (fun pair => termMeasure substitution pair.2)).sum := by
      simp [List.map_map, Function.comp_def]
    _ < (pairs.map (fun pair => termMeasure substitution pair.1)).sum := sumsLt
    _ = (((pairs.map Prod.fst).map
          (termMeasure substitution)).sum) := by
      simp [List.map_map, Function.comp_def]
    _ = ((termsToList head.arguments).map
          (termMeasure substitution)).sum := by rw [firsts]

mutual
  def groundTermToTerm : GroundTerm → Term
    | .atom name => .atom name
    | .integer value => .integer value
    | .app constructor arguments =>
        .app constructor (groundTermsToTerms arguments)

  def groundTermsToTerms : GroundTerms → Terms
    | .nil => .nil
    | .cons head tail =>
        .cons (groundTermToTerm head) (groundTermsToTerms tail)
end

def groundAtomToAtom (atom : GroundAtom) : Atom :=
  { relation := atom.relation
    arguments := groundTermsToTerms atom.arguments }

def groundAtomMeasure (atom : GroundAtom) : Nat :=
  atomMeasure (fun v => .var v) (groundAtomToAtom atom)

def lookupGround : Nat → Substitution → Option GroundTerm
  | _, [] => none
  | identifier, (candidate, value) :: rest =>
      if identifier = candidate then some value
      else lookupGround identifier rest

def bindGround (identifier : Nat) (value : GroundTerm)
    (substitution : Substitution) : Option Substitution :=
  match lookupGround identifier substitution with
  | none => some ((identifier, value) :: substitution)
  | some previous => if previous = value then some substitution else none

mutual
  def matchGroundTerm : Term → GroundTerm → Substitution → Option Substitution
    | .var identifier, value, substitution =>
        bindGround identifier value substitution
    | .atom expected, .atom actual, substitution =>
        if expected = actual then some substitution else none
    | .integer expected, .integer actual, substitution =>
        if expected = actual then some substitution else none
    | .app expectedConstructor expectedArguments,
        .app actualConstructor actualArguments, substitution =>
        if expectedConstructor != actualConstructor then none
        else matchGroundTerms expectedArguments actualArguments substitution
    | _, _, _ => none

  def matchGroundTerms :
      Terms → GroundTerms → Substitution → Option Substitution
    | .nil, .nil, substitution => some substitution
    | .cons expectedHead expectedTail, .cons actualHead actualTail,
        substitution => do
        let afterHead ← matchGroundTerm expectedHead actualHead substitution
        matchGroundTerms expectedTail actualTail afterHead
    | _, _, _ => none
end

def matchGroundAtom (pattern : Atom) (target : GroundAtom) :
    Option Substitution :=
  if pattern.relation != target.relation then none
  else matchGroundTerms pattern.arguments target.arguments []

def instantiateGroundBody (substitution : Substitution)
    (body : List Atom) : Option (List GroundAtom) :=
  instantiateAtoms substitution body

/-- Parser rules are outside this checker.  Every other admitted rule is a
ground fact or a conjunction of range-safe structurally decreasing recursive
premises in one relation.  Cross-relation recursion requires a future explicit
stratification certificate and therefore fails closed here. -/
def sideRuleAdmitted (parseRelation : String) (rule : Rule) : Bool :=
  if rule.head.relation = parseRelation then true
  else if rule.body.isEmpty then atomVariables rule.head = []
  else
    rule.body.all fun premise =>
      premise.relation != parseRelation &&
        premiseStructurallyDecreases rule.head premise

def sideProgramAdmitted (program : Program) (parseRelation : String) : Bool :=
  program.all (sideRuleAdmitted parseRelation)

/-- Total query-directed certificate search for the admitted side fragment.
Every recursive call must pass the semantic size guard.  The assembled proof
is replayed before it can escape, so this producer is never an authority. -/
private def searchSide (program : Program) (parseRelation : String)
    (goal : GroundAtom) : Option Certificate :=
  program.findSome? fun rule =>
    if rule.head.relation = parseRelation then none
    else if sideRuleAdmitted parseRelation rule != true then none
    else do
      let substitution ← matchGroundAtom rule.head goal
      let premises ← instantiateGroundBody substitution rule.body
      let children ← premises.mapM fun premise =>
        if _smaller : groundAtomMeasure premise < groundAtomMeasure goal then
          searchSide program parseRelation premise
        else none
      let certificate := Certificate.node rule substitution
        (Certificates.ofList children)
      if replay program (groundAtomMeasure goal + 1) goal certificate then
        some certificate
      else none
termination_by groundAtomMeasure goal
decreasing_by exact _smaller

/-- The public side-proof producer has a deliberately narrow authority
boundary: whatever the internal search returns is replayed independently
against the admitted program before it can escape. -/
def proveSide (program : Program) (parseRelation : String)
    (goal : GroundAtom) : Option Certificate :=
  match searchSide program parseRelation goal with
  | none => none
  | some certificate =>
      if replay program (groundAtomMeasure goal + 1) goal certificate then
        some certificate
      else none

theorem proveSide_replays {program : Program} {parseRelation : String}
    {goal : GroundAtom} {certificate : Certificate}
    (produced : proveSide program parseRelation goal = some certificate) :
    replay program (groundAtomMeasure goal + 1) goal certificate = true := by
  simp only [proveSide] at produced
  split at produced
  next => simp at produced
  next candidate =>
    split at produced
    next replayed =>
      simp only [Option.some.injEq] at produced
      simpa [produced] using replayed
    next => simp at produced

theorem proveSide_derivesWithin {program : Program} {parseRelation : String}
    {goal : GroundAtom} {certificate : Certificate}
    (produced : proveSide program parseRelation goal = some certificate) :
    DerivesWithin program (groundAtomMeasure goal + 1) goal :=
  (replay_iff_derivesWithin program (groundAtomMeasure goal + 1) goal).mp
    ⟨certificate, proveSide_replays produced⟩

/-! ## Executable positive and negative controls -/

def factRule : Rule :=
  { name := "fact"
    head := { relation := "side", arguments := Terms.ofList [.atom "a"] }
    body := [] }

def decreasingRule : Rule :=
  { name := "decreasing"
    head :=
      { relation := "side"
        arguments := Terms.ofList [.app "wrap" (Terms.ofList [.var 0]), .var 1] }
    body :=
      [{ relation := "side", arguments := Terms.ofList [.var 0, .var 1] }] }

def nonGroundFactRule : Rule :=
  { name := "non-ground-fact"
    head := { relation := "side", arguments := Terms.ofList [.var 0] }
    body := [] }

def selfCycleRule : Rule :=
  { name := "self-cycle"
    head := { relation := "side", arguments := Terms.ofList [.var 0] }
    body := [{ relation := "side", arguments := Terms.ofList [.var 0] }] }

def growthRule : Rule :=
  { name := "growth"
    head := { relation := "side", arguments := Terms.ofList [.var 0] }
    body :=
      [{ relation := "side"
         arguments := Terms.ofList [.app "wrap" (Terms.ofList [.var 0])] }] }

def escapingVariableRule : Rule :=
  { name := "escaping-variable"
    head := { relation := "side", arguments := Terms.ofList [.var 0] }
    body := [{ relation := "side", arguments := Terms.ofList [.var 1] }] }

def parseCallingSideRule : Rule :=
  { name := "parse-calling-side"
    head :=
      { relation := "side"
        arguments := Terms.ofList [.app "wrap" (Terms.ofList [.var 0])] }
    body := [{ relation := "parse", arguments := Terms.ofList [.var 0] }] }

def crossRelationRule : Rule :=
  { name := "cross-relation"
    head :=
      { relation := "side"
        arguments := Terms.ofList [.app "wrap" (Terms.ofList [.var 0])] }
    body := [{ relation := "other", arguments := Terms.ofList [.var 0] }] }

def baseFactRule : Rule :=
  { name := "base-fact"
    head :=
      { relation := "side"
        arguments := Terms.ofList [.atom "base", .atom "evidence"] }
    body := [] }

def terminatingSideProgram : Program := [decreasingRule, baseFactRule]

def nestedSideGoal : GroundAtom :=
  { relation := "side"
    arguments := GroundTerms.ofList [
      .app "wrap" (GroundTerms.ofList [
        .app "wrap" (GroundTerms.ofList [.atom "base"])]),
      .atom "evidence"] }

def cyclicSideProgram : Program := [selfCycleRule]

private def baseSideGoal : GroundAtom :=
  { relation := "side"
    arguments := GroundTerms.ofList [.atom "base", .atom "evidence"] }

private def wrappedSideGoal : GroundAtom :=
  { relation := "side"
    arguments := GroundTerms.ofList [
      .app "wrap" (GroundTerms.ofList [.atom "base"]), .atom "evidence"] }

private def baseSideCertificate : Certificate :=
  .node baseFactRule [] .nil

private def wrappedSideSubstitution : Substitution :=
  [(1, .atom "evidence"), (0, .atom "base")]

private def nestedSideSubstitution : Substitution :=
  [(1, .atom "evidence"),
    (0, .app "wrap" (GroundTerms.ofList [.atom "base"]))]

private def wrappedSideCertificate : Certificate :=
  .node decreasingRule wrappedSideSubstitution
    (.cons baseSideCertificate .nil)

private def nestedSideCertificate : Certificate :=
  .node decreasingRule nestedSideSubstitution
    (.cons wrappedSideCertificate .nil)

private theorem decreasing_rule_admitted :
    sideRuleAdmitted "parse" decreasingRule = true := by
  decide

private theorem decreasing_matches_wrapped :
    matchGroundAtom decreasingRule.head wrappedSideGoal =
      some wrappedSideSubstitution := by
  decide

private theorem decreasing_body_at_wrapped :
    instantiateGroundBody wrappedSideSubstitution decreasingRule.body =
      some [baseSideGoal] := by
  decide

private theorem base_measure_lt_wrapped :
    groundAtomMeasure baseSideGoal < groundAtomMeasure wrappedSideGoal := by
  decide

private theorem wrapped_certificate_replays :
    replay [decreasingRule, baseFactRule]
      (groundAtomMeasure wrappedSideGoal + 1)
      wrappedSideGoal wrappedSideCertificate = true := by
  decide

private theorem decreasing_matches_nested :
    matchGroundAtom decreasingRule.head nestedSideGoal =
      some nestedSideSubstitution := by
  decide

private theorem decreasing_body_at_nested :
    instantiateGroundBody nestedSideSubstitution decreasingRule.body =
      some [wrappedSideGoal] := by
  decide

private theorem wrapped_measure_lt_nested :
    groundAtomMeasure wrappedSideGoal < groundAtomMeasure nestedSideGoal := by
  decide

private theorem nested_certificate_replays :
    replay [decreasingRule, baseFactRule]
      (groundAtomMeasure nestedSideGoal + 1)
      nestedSideGoal nestedSideCertificate = true := by
  decide

private theorem searchSide_terminating_base :
    searchSide [decreasingRule, baseFactRule] "parse" baseSideGoal =
      some baseSideCertificate := by
  rw [searchSide.eq_1]
  decide

private theorem searchSide_terminating_wrapped :
    searchSide [decreasingRule, baseFactRule] "parse" wrappedSideGoal =
      some wrappedSideCertificate := by
  rw [searchSide.eq_1]
  simp [List.findSome?, decreasing_rule_admitted, decreasing_matches_wrapped,
    decreasing_body_at_wrapped, base_measure_lt_wrapped,
    searchSide_terminating_base]
  have certificateEq :
      Certificate.node decreasingRule wrappedSideSubstitution
          (Certificates.ofList [baseSideCertificate]) =
        wrappedSideCertificate := rfl
  rw [certificateEq, wrapped_certificate_replays]
  simp [decreasingRule]

private theorem searchSide_terminating_nested :
    searchSide [decreasingRule, baseFactRule] "parse" nestedSideGoal =
      some nestedSideCertificate := by
  rw [searchSide.eq_1]
  simp [List.findSome?, decreasing_rule_admitted, decreasing_matches_nested,
    decreasing_body_at_nested, wrapped_measure_lt_nested,
    searchSide_terminating_wrapped]
  have certificateEq :
      Certificate.node decreasingRule nestedSideSubstitution
          (Certificates.ofList [wrappedSideCertificate]) =
        nestedSideCertificate := rfl
  rw [certificateEq, nested_certificate_replays]
  simp [decreasingRule]

theorem total_side_search_finds_nested_proof :
    (proveSide terminatingSideProgram "parse" nestedSideGoal).isSome = true := by
  simp [proveSide, terminatingSideProgram, searchSide_terminating_nested,
    nested_certificate_replays]

theorem total_side_search_result_replays :
    (match proveSide terminatingSideProgram "parse" nestedSideGoal with
    | none => false
    | some certificate =>
        replay terminatingSideProgram (groundAtomMeasure nestedSideGoal + 1)
          nestedSideGoal certificate) = true := by
  cases produced : proveSide terminatingSideProgram "parse" nestedSideGoal with
  | none =>
      have := total_side_search_finds_nested_proof
      simp [produced] at this
  | some certificate =>
      exact proveSide_replays produced

theorem unadmitted_cycle_has_no_side_proof :
    proveSide cyclicSideProgram "parse"
      { relation := "side", arguments := GroundTerms.ofList [.atom "base"] } =
        none := by
  rw [proveSide, searchSide.eq_1]
  have rejected : sideRuleAdmitted "parse" selfCycleRule = false := by decide
  simp [cyclicSideProgram, rejected]

private theorem searchSide_decreasing_base :
    searchSide [decreasingRule] "parse" baseSideGoal = none := by
  rw [searchSide.eq_1]
  decide

private theorem searchSide_decreasing_wrapped :
    searchSide [decreasingRule] "parse" wrappedSideGoal = none := by
  rw [searchSide.eq_1]
  simp [List.findSome?, decreasing_rule_admitted,
    decreasing_matches_wrapped, decreasing_body_at_wrapped,
    base_measure_lt_wrapped, searchSide_decreasing_base]

private theorem searchSide_decreasing_nested :
    searchSide [decreasingRule] "parse" nestedSideGoal = none := by
  rw [searchSide.eq_1]
  simp [List.findSome?, decreasing_rule_admitted,
    decreasing_matches_nested, decreasing_body_at_nested,
    wrapped_measure_lt_nested, searchSide_decreasing_wrapped]

theorem missing_base_fact_has_no_side_proof :
    proveSide [decreasingRule] "parse" nestedSideGoal = none := by
  simp [proveSide, searchSide_decreasing_nested]

theorem ground_fact_is_admitted :
    sideRuleAdmitted "parse" factRule = true := by
  decide

theorem structurally_decreasing_rule_is_admitted :
    sideRuleAdmitted "parse" decreasingRule = true := by
  decide

theorem nonground_fact_is_rejected :
    sideRuleAdmitted "parse" nonGroundFactRule = false := by
  decide

theorem self_cycle_is_rejected :
    sideRuleAdmitted "parse" selfCycleRule = false := by
  decide

theorem growth_is_rejected :
    sideRuleAdmitted "parse" growthRule = false := by
  decide

theorem escaping_variable_is_rejected :
    sideRuleAdmitted "parse" escapingVariableRule = false := by
  decide

theorem parse_calling_side_rule_is_rejected :
    sideRuleAdmitted "parse" parseCallingSideRule = false := by
  decide

theorem cross_relation_without_stratum_is_rejected :
    sideRuleAdmitted "parse" crossRelationRule = false := by
  decide

end Mettapedia.GSLT.Parsing.HornSideAdmission
