import Mettapedia.GSLT.Parsing.HornReachableClosure
import Mettapedia.GSLT.Parsing.HornSemanticEnumeration

/-!
# Child-grammar extraction directly from admitted Horn programs

For a ground parser grammar, the compiler constructs an ordinary four-argument
parser query, enumerates applicable admitted rule heads with apart-renamed
occurs-checked unification, applies each resulting substitution to recursive
parser calls in the corresponding source body, and retains only ground child
grammar terms.  No grammar constructor or guest-language name is interpreted.

The fuel is a compiler search bound, not syntax semantics.  The surrounding
reachable-closure admission still rejects a result whose frontier is not
closed.
-/

namespace Mettapedia.GSLT.Parsing.HornProgramChildren

open HornCertificate HornUnification HornHeadEnumeration HornSpecialization

theorem ofList_termsToList (terms : Terms) :
    Terms.ofList (termsToList terms) = terms := by
  fun_induction termsToList terms <;> simp_all [Terms.ofList]

def compilerAtomArguments
    (atom : Mettapedia.Logic.LP.Atom compilerSignature) :
    List (Mettapedia.Logic.LP.Term compilerSignature) :=
  List.ofFn atom.args

def parserQuery (parseRelation : String) (grammar : Term) : Atom :=
  { relation := parseRelation
    arguments := Terms.ofList [grammar, .var 0, .var 1, .var 2] }

def decodeCompilerTerm :
    Mettapedia.Logic.LP.Term compilerSignature → Term
  | .var v => .var v.identifier
  | .const (.atom name) => .atom name
  | .const (.integer value) => .integer value
  | .app function arguments =>
      .app function.name <| Terms.ofList <|
        (List.finRange function.arity).map fun index =>
          decodeCompilerTerm (arguments index)
termination_by term => term.size
decreasing_by
  exact Mettapedia.Logic.LP.Term.size_subterm index

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

def compilerTermGround
    (term : Mettapedia.Logic.LP.Term compilerSignature) : Bool :=
  decide (term.freeVars = ∅)

theorem compilerTermGround_iff
    (term : Mettapedia.Logic.LP.Term compilerSignature) :
    compilerTermGround term = true ↔ term.isGround := by
  simp [compilerTermGround,
    Mettapedia.Logic.LP.Term.isGround_iff_freeVars_empty]

def decodeGroundCompilerTerm
    (term : Mettapedia.Logic.LP.Term compilerSignature) : Option Term :=
  if compilerTermGround term then some (decodeCompilerTerm term) else none

theorem decodeGroundCompilerTerm_isGround
    {source : Mettapedia.Logic.LP.Term compilerSignature} {target : Term}
    (decoded : decodeGroundCompilerTerm source = some target) :
    source.isGround := by
  simp only [decodeGroundCompilerTerm] at decoded
  split at decoded
  next ground => exact (compilerTermGround_iff source).mp ground
  next notGround => simp at decoded

/-- Applying a substitution to an encoded ground source term cannot change it,
so decoding the compiler term recovers the unique authored source term.  This
is the representation bridge used by executable child discovery; no property
of a particular unification algorithm is involved. -/
theorem decodeGroundCompilerTerm_apply_encodeScopedTerm_of_ground
    (substitution : Mettapedia.Logic.LP.Subst compilerSignature)
    (origin : VariableOrigin) (source : Term)
    (ground : (encodeScopedTerm origin source).isGround) :
    decodeGroundCompilerTerm
        (substitution.applyTerm (encodeScopedTerm origin source)) =
      some source := by
  rw [applyTerm_eq_self_of_isGround substitution ground]
  simp only [decodeGroundCompilerTerm]
  rw [if_pos ((compilerTermGround_iff _).mpr ground)]
  exact congrArg some (decodeCompilerTerm_encodeScopedTerm origin source)

def instantiatedChildGrammar (parseRelation : String)
    (headMatch : HeadMatch) (atom : Atom) : Option Term :=
  if atom.relation != parseRelation then none
  else
    match termsToList atom.arguments with
    | [grammar, _, _, _] =>
        decodeGroundCompilerTerm <|
          headMatch.substitution.applyTerm (encodeScopedTerm .rule grammar)
    | _ => none

def matchedChildren (parseRelation : String) (headMatch : HeadMatch) : List Term :=
  headMatch.rule.body.filterMap (instantiatedChildGrammar parseRelation headMatch)

/-- A recursive child grammar may depend only on variables present in the
parser head's grammar argument.  Otherwise head matching can leave a child
variable unconstrained and a finite compiler cannot soundly treat the missing
ground instance as absence. -/
def recursiveGrammarAtomSafe (parseRelation : String)
    (headGrammar : Term) (atom : Atom) : Bool :=
  if atom.relation != parseRelation then true
  else
    match termsToList atom.arguments with
    | [child, _, _, _] =>
        decide ((encodeScopedTerm .rule child).freeVars ⊆
          (encodeScopedTerm .rule headGrammar).freeVars)
    | _ => false

def parserRuleSafe (parseRelation : String) (rule : Rule) : Bool :=
  if rule.head.relation != parseRelation then true
  else
    match termsToList rule.head.arguments with
    | [headGrammar, _, _, _] =>
        rule.body.all (recursiveGrammarAtomSafe parseRelation headGrammar)
    | _ => false

def parserProgramSafe (program : Program) (parseRelation : String) : Bool :=
  program.all (parserRuleSafe parseRelation)

theorem parserProgramSafe_rule
    {program : Program} {parseRelation : String} {rule : Rule}
    (safe : parserProgramSafe program parseRelation = true)
    (member : rule ∈ program) :
    parserRuleSafe parseRelation rule = true := by
  exact (List.all_eq_true.mp safe) rule member

theorem recursiveGrammarAtomSafe_iff
    {parseRelation : String} {headGrammar child input value output : Term}
    {atom : Atom}
    (relation : atom.relation = parseRelation)
    (arguments : termsToList atom.arguments = [child, input, value, output]) :
    recursiveGrammarAtomSafe parseRelation headGrammar atom = true ↔
      (encodeScopedTerm .rule child).freeVars ⊆
        (encodeScopedTerm .rule headGrammar).freeVars := by
  simp [recursiveGrammarAtomSafe, relation, arguments]

theorem parserRuleSafe_body
    {parseRelation : String} {rule : Rule}
    {headGrammar headInput headValue headOutput : Term}
    (relation : rule.head.relation = parseRelation)
    (arguments : termsToList rule.head.arguments =
      [headGrammar, headInput, headValue, headOutput])
    (safe : parserRuleSafe parseRelation rule = true)
    {atom : Atom} (member : atom ∈ rule.body) :
    recursiveGrammarAtomSafe parseRelation headGrammar atom = true := by
  have allSafe :
      rule.body.all (recursiveGrammarAtomSafe parseRelation headGrammar) = true := by
    simpa [parserRuleSafe, relation, arguments] using safe
  exact (List.all_eq_true.mp allSafe) atom member

theorem HeadMatches.headGrammar_instantiation
    {parseRelation : String} {parentGrammar headGrammar input value output : Term}
    {maximumFuel : Nat} {rule : Rule} {headMatch : HeadMatch}
    (matched : HeadMatches (parserQuery parseRelation parentGrammar)
      maximumFuel rule headMatch)
    (arguments : termsToList rule.head.arguments =
      [headGrammar, input, value, output]) :
    headMatch.substitution.applyTerm
        (encodeScopedTerm .query parentGrammar) =
      headMatch.substitution.applyTerm
        (encodeScopedTerm .rule headGrammar) := by
  have argumentTerms : rule.head.arguments =
      Terms.ofList [headGrammar, input, value, output] := by
    rw [← ofList_termsToList rule.head.arguments, arguments]
  have atomEquality := congrArg compilerAtomArguments matched.sound.2.2
  simp [compilerAtomArguments, Mettapedia.Logic.LP.Subst.applyAtom,
    parserQuery, encodeScopedAtom, argumentTerms] at atomEquality
  exact (List.cons.inj atomEquality).1

theorem HeadMatches.headGrammar_ground
    {parseRelation : String} {parentGrammar headGrammar input value output : Term}
    {maximumFuel : Nat} {rule : Rule} {headMatch : HeadMatch}
    (matched : HeadMatches (parserQuery parseRelation parentGrammar)
      maximumFuel rule headMatch)
    (arguments : termsToList rule.head.arguments =
      [headGrammar, input, value, output])
    (parentGround : (encodeScopedTerm .query parentGrammar).isGround) :
    (headMatch.substitution.applyTerm
      (encodeScopedTerm .rule headGrammar)).isGround := by
  rw [← Mettapedia.GSLT.Parsing.HornProgramChildren.HeadMatches.headGrammar_instantiation
    matched arguments]
  rw [applyTerm_eq_self_of_isGround headMatch.substitution parentGround]
  exact parentGround

/-- Range safety makes every recursive child ground under the compiler's MGU,
so the executable extractor cannot silently drop it. -/
theorem safeMatchedChild_is_decoded
    {parseRelation : String} {parentGrammar headGrammar : Term}
    {headInput headValue headOutput child input value output : Term}
    {maximumFuel : Nat} {rule : Rule} {headMatch : HeadMatch} {atom : Atom}
    (matched : HeadMatches (parserQuery parseRelation parentGrammar)
      maximumFuel rule headMatch)
    (headRelation : rule.head.relation = parseRelation)
    (headArguments : termsToList rule.head.arguments =
      [headGrammar, headInput, headValue, headOutput])
    (safe : parserRuleSafe parseRelation rule = true)
    (member : atom ∈ rule.body)
    (childRelation : atom.relation = parseRelation)
    (childArguments : termsToList atom.arguments = [child, input, value, output])
    (parentGround : (encodeScopedTerm .query parentGrammar).isGround) :
    instantiatedChildGrammar parseRelation headMatch atom =
      some (decodeCompilerTerm <|
        headMatch.substitution.applyTerm (encodeScopedTerm .rule child)) := by
  have atomSafe := parserRuleSafe_body headRelation headArguments safe member
  have subset := (recursiveGrammarAtomSafe_iff childRelation childArguments).mp
    atomSafe
  have headGround :=
    Mettapedia.GSLT.Parsing.HornProgramChildren.HeadMatches.headGrammar_ground
      matched headArguments parentGround
  have childGround := applyTerm_ground_of_freeVars_subset
    headMatch.substitution subset headGround
  have groundCheck := (compilerTermGround_iff
    (headMatch.substitution.applyTerm (encodeScopedTerm .rule child))).mpr
      childGround
  simp [instantiatedChildGrammar, childRelation, childArguments,
    decodeGroundCompilerTerm, groundCheck]

def programChildren (program : Program) (parseRelation : String)
    (maximumFuel : Nat) (grammar : Term) : List Term :=
  ((matchHeads program (parserQuery parseRelation grammar) maximumFuel).flatMap
    (matchedChildren parseRelation)).dedup

theorem mem_programChildren_iff
    {program : Program} {parseRelation : String} {maximumFuel : Nat}
    {grammar child : Term} :
    child ∈ programChildren program parseRelation maximumFuel grammar ↔
      ∃ headMatch ∈
          matchHeads program (parserQuery parseRelation grammar) maximumFuel,
        ∃ atom ∈ headMatch.rule.body,
          instantiatedChildGrammar parseRelation headMatch atom = some child := by
  simp [programChildren, matchedChildren, List.mem_flatMap, List.mem_filterMap]

/-- Every extracted child cites an admitted source rule, a successful
apart-renamed head match, and the exact recursive body atom that produced it. -/
theorem programChild_is_source_derived
    {program : Program} {parseRelation : String} {maximumFuel : Nat}
    {grammar child : Term}
    (member : child ∈ programChildren program parseRelation maximumFuel grammar) :
    ∃ rule ∈ program,
      ∃ headMatch,
        HeadMatches (parserQuery parseRelation grammar) maximumFuel rule headMatch ∧
        ∃ atom ∈ rule.body,
          instantiatedChildGrammar parseRelation headMatch atom = some child := by
  obtain ⟨headMatch, matchMember, atom, atomMember, decoded⟩ :=
    mem_programChildren_iff.mp member
  obtain ⟨rule, ruleMember, matched⟩ :=
    matchHeads_sound program (parserQuery parseRelation grammar) maximumFuel
      headMatch matchMember
  have ruleEq := matched.sound.1
  subst rule
  exact ⟨headMatch.rule, ruleMember, headMatch, matched, atom, atomMember, decoded⟩

/-- Conversely, every ground recursive child decoded from an enumerated source
head match is present in the executable child list. -/
theorem programChild_complete_of_match
    {program : Program} {parseRelation : String} {maximumFuel : Nat}
    {grammar child : Term} {headMatch : HeadMatch} {atom : Atom}
    (matchMember : headMatch ∈
      matchHeads program (parserQuery parseRelation grammar) maximumFuel)
    (atomMember : atom ∈ headMatch.rule.body)
    (decoded : instantiatedChildGrammar parseRelation headMatch atom = some child) :
    child ∈ programChildren program parseRelation maximumFuel grammar :=
  mem_programChildren_iff.mpr
    ⟨headMatch, matchMember, atom, atomMember, decoded⟩

theorem safeMatchedChild_mem_programChildren
    {program : Program} {parseRelation : String}
    {parentGrammar headGrammar : Term}
    {headInput headValue headOutput child input value output : Term}
    {maximumFuel : Nat} {rule : Rule} {headMatch : HeadMatch} {atom : Atom}
    (matchMember : headMatch ∈
      matchHeads program (parserQuery parseRelation parentGrammar) maximumFuel)
    (matched : HeadMatches (parserQuery parseRelation parentGrammar)
      maximumFuel rule headMatch)
    (headRelation : rule.head.relation = parseRelation)
    (headArguments : termsToList rule.head.arguments =
      [headGrammar, headInput, headValue, headOutput])
    (safe : parserRuleSafe parseRelation rule = true)
    (member : atom ∈ rule.body)
    (childRelation : atom.relation = parseRelation)
    (childArguments : termsToList atom.arguments = [child, input, value, output])
    (parentGround : (encodeScopedTerm .query parentGrammar).isGround) :
    decodeCompilerTerm
        (headMatch.substitution.applyTerm (encodeScopedTerm .rule child)) ∈
      programChildren program parseRelation maximumFuel parentGrammar := by
  have atomMember : atom ∈ headMatch.rule.body := by
    simpa [matched.sound.1] using member
  apply programChild_complete_of_match matchMember atomMember
  exact safeMatchedChild_is_decoded matched headRelation headArguments safe member
    childRelation childArguments parentGround

/-- A child successfully decoded from the compiler MGU is invariant under
every more-specific semantic unifier of the same query and source head. -/
theorem instantiatedChildGrammar_fixed_under_unifier
    {parseRelation : String} {maximumFuel : Nat} {rule : Rule}
    {headMatch : HeadMatch} {atom : Atom} {child : Term}
    {parentGrammar childPattern input value output : Term}
    (matched : HeadMatches (parserQuery parseRelation parentGrammar)
      maximumFuel rule headMatch)
    (arguments : termsToList atom.arguments =
      [childPattern, input, value, output])
    (decoded : instantiatedChildGrammar parseRelation headMatch atom = some child)
    (candidate : Mettapedia.Logic.LP.Subst compilerSignature)
    (unifies :
      candidate.applyAtom
          (encodeScopedAtom .query (parserQuery parseRelation parentGrammar)) =
        candidate.applyAtom (encodeScopedAtom .rule rule.head)) :
    candidate.applyTerm (encodeScopedTerm .rule childPattern) =
      headMatch.substitution.applyTerm
        (encodeScopedTerm .rule childPattern) := by
  have ground :
      (headMatch.substitution.applyTerm
        (encodeScopedTerm .rule childPattern)).isGround := by
    unfold instantiatedChildGrammar at decoded
    split at decoded
    next mismatch => simp at decoded
    next relationMatch =>
      rw [arguments] at decoded
      exact decodeGroundCompilerTerm_isGround decoded
  exact matched.factorGroundTerm candidate unifies
    (encodeScopedTerm .rule childPattern) ground

theorem safeMatchedChild_fixed_under_unifier
    {parseRelation : String} {parentGrammar headGrammar : Term}
    {headInput headValue headOutput child input value output : Term}
    {maximumFuel : Nat} {rule : Rule} {headMatch : HeadMatch} {atom : Atom}
    (matched : HeadMatches (parserQuery parseRelation parentGrammar)
      maximumFuel rule headMatch)
    (headRelation : rule.head.relation = parseRelation)
    (headArguments : termsToList rule.head.arguments =
      [headGrammar, headInput, headValue, headOutput])
    (safe : parserRuleSafe parseRelation rule = true)
    (member : atom ∈ rule.body)
    (childRelation : atom.relation = parseRelation)
    (childArguments : termsToList atom.arguments = [child, input, value, output])
    (parentGround : (encodeScopedTerm .query parentGrammar).isGround)
    (candidate : Mettapedia.Logic.LP.Subst compilerSignature)
    (unifies :
      candidate.applyAtom
          (encodeScopedAtom .query (parserQuery parseRelation parentGrammar)) =
        candidate.applyAtom (encodeScopedAtom .rule rule.head)) :
    candidate.applyTerm (encodeScopedTerm .rule child) =
      headMatch.substitution.applyTerm (encodeScopedTerm .rule child) := by
  have decoded := safeMatchedChild_is_decoded matched headRelation headArguments
    safe member childRelation childArguments parentGround
  exact instantiatedChildGrammar_fixed_under_unifier matched childArguments
    decoded candidate unifies

/-! ## Fuel-free production child discovery -/

def instantiatedChildGrammarTotal (parseRelation : String)
    (headMatch : TotalHeadMatch) (atom : Atom) : Option Term :=
  if atom.relation != parseRelation then none
  else
    match termsToList atom.arguments with
    | [grammar, _, _, _] =>
        decodeGroundCompilerTerm <|
          headMatch.substitution.applyTerm (encodeScopedTerm .rule grammar)
    | _ => none

def matchedChildrenTotal (parseRelation : String)
    (headMatch : TotalHeadMatch) : List Term :=
  headMatch.rule.body.filterMap
    (instantiatedChildGrammarTotal parseRelation headMatch)

def programChildrenTotal (program : Program) (parseRelation : String)
    (grammar : Term) : List Term :=
  ((matchHeadsTotal program (parserQuery parseRelation grammar)).flatMap
    (matchedChildrenTotal parseRelation)).dedup

theorem mem_programChildrenTotal_iff
    {program : Program} {parseRelation : String} {grammar child : Term} :
    child ∈ programChildrenTotal program parseRelation grammar ↔
      ∃ headMatch ∈
          matchHeadsTotal program (parserQuery parseRelation grammar),
        ∃ atom ∈ headMatch.rule.body,
          instantiatedChildGrammarTotal parseRelation headMatch atom =
            some child := by
  simp [programChildrenTotal, matchedChildrenTotal, List.mem_flatMap,
    List.mem_filterMap]

theorem TotalHeadMatches.headGrammar_instantiation
    {parseRelation : String} {parentGrammar headGrammar input value output : Term}
    {rule : Rule} {headMatch : TotalHeadMatch}
    (matched : TotalHeadMatches (parserQuery parseRelation parentGrammar)
      rule headMatch)
    (arguments : termsToList rule.head.arguments =
      [headGrammar, input, value, output]) :
    headMatch.substitution.applyTerm
        (encodeScopedTerm .query parentGrammar) =
      headMatch.substitution.applyTerm
        (encodeScopedTerm .rule headGrammar) := by
  have argumentTerms : rule.head.arguments =
      Terms.ofList [headGrammar, input, value, output] := by
    rw [← ofList_termsToList rule.head.arguments, arguments]
  have atomEquality := congrArg compilerAtomArguments matched.sound.2
  simp [compilerAtomArguments, Mettapedia.Logic.LP.Subst.applyAtom,
    parserQuery, encodeScopedAtom, argumentTerms] at atomEquality
  exact (List.cons.inj atomEquality).1

theorem TotalHeadMatches.headGrammar_ground
    {parseRelation : String} {parentGrammar headGrammar input value output : Term}
    {rule : Rule} {headMatch : TotalHeadMatch}
    (matched : TotalHeadMatches (parserQuery parseRelation parentGrammar)
      rule headMatch)
    (arguments : termsToList rule.head.arguments =
      [headGrammar, input, value, output])
    (parentGround : (encodeScopedTerm .query parentGrammar).isGround) :
    (headMatch.substitution.applyTerm
      (encodeScopedTerm .rule headGrammar)).isGround := by
  rw [← Mettapedia.GSLT.Parsing.HornProgramChildren.TotalHeadMatches.headGrammar_instantiation
    matched arguments]
  rw [applyTerm_eq_self_of_isGround headMatch.substitution parentGround]
  exact parentGround

theorem safeTotalMatchedChild_is_decoded
    {parseRelation : String} {parentGrammar headGrammar : Term}
    {headInput headValue headOutput child input value output : Term}
    {rule : Rule} {headMatch : TotalHeadMatch} {atom : Atom}
    (matched : TotalHeadMatches (parserQuery parseRelation parentGrammar)
      rule headMatch)
    (headRelation : rule.head.relation = parseRelation)
    (headArguments : termsToList rule.head.arguments =
      [headGrammar, headInput, headValue, headOutput])
    (safe : parserRuleSafe parseRelation rule = true)
    (member : atom ∈ rule.body)
    (childRelation : atom.relation = parseRelation)
    (childArguments : termsToList atom.arguments = [child, input, value, output])
    (parentGround : (encodeScopedTerm .query parentGrammar).isGround) :
    instantiatedChildGrammarTotal parseRelation headMatch atom =
      some (decodeCompilerTerm <|
        headMatch.substitution.applyTerm (encodeScopedTerm .rule child)) := by
  have atomSafe := parserRuleSafe_body headRelation headArguments safe member
  have subset := (recursiveGrammarAtomSafe_iff childRelation childArguments).mp
    atomSafe
  have headGround :=
    Mettapedia.GSLT.Parsing.HornProgramChildren.TotalHeadMatches.headGrammar_ground
      matched headArguments parentGround
  have childGround := applyTerm_ground_of_freeVars_subset
    headMatch.substitution subset headGround
  have groundCheck := (compilerTermGround_iff
    (headMatch.substitution.applyTerm (encodeScopedTerm .rule child))).mpr
      childGround
  simp [instantiatedChildGrammarTotal, childRelation, childArguments,
    decodeGroundCompilerTerm, groundCheck]

theorem safeTotalMatchedChild_mem_programChildren
    {program : Program} {parseRelation : String}
    {parentGrammar headGrammar : Term}
    {headInput headValue headOutput child input value output : Term}
    {rule : Rule} {headMatch : TotalHeadMatch} {atom : Atom}
    (matchMember : headMatch ∈
      matchHeadsTotal program (parserQuery parseRelation parentGrammar))
    (matched : TotalHeadMatches (parserQuery parseRelation parentGrammar)
      rule headMatch)
    (headRelation : rule.head.relation = parseRelation)
    (headArguments : termsToList rule.head.arguments =
      [headGrammar, headInput, headValue, headOutput])
    (safe : parserRuleSafe parseRelation rule = true)
    (member : atom ∈ rule.body)
    (childRelation : atom.relation = parseRelation)
    (childArguments : termsToList atom.arguments = [child, input, value, output])
    (parentGround : (encodeScopedTerm .query parentGrammar).isGround) :
    decodeCompilerTerm
        (headMatch.substitution.applyTerm (encodeScopedTerm .rule child)) ∈
      programChildrenTotal program parseRelation parentGrammar := by
  have atomMember : atom ∈ headMatch.rule.body := by
    simpa [matched.sound.1] using member
  apply mem_programChildrenTotal_iff.mpr
  exact ⟨headMatch, matchMember, atom, atomMember,
    safeTotalMatchedChild_is_decoded matched headRelation headArguments safe
      member childRelation childArguments parentGround⟩

theorem safeTotalMatchedChild_fixed_under_unifier
    {parseRelation : String} {parentGrammar headGrammar : Term}
    {headInput headValue headOutput child input value output : Term}
    {rule : Rule} {headMatch : TotalHeadMatch} {atom : Atom}
    (matched : TotalHeadMatches (parserQuery parseRelation parentGrammar)
      rule headMatch)
    (headRelation : rule.head.relation = parseRelation)
    (headArguments : termsToList rule.head.arguments =
      [headGrammar, headInput, headValue, headOutput])
    (safe : parserRuleSafe parseRelation rule = true)
    (member : atom ∈ rule.body)
    (childRelation : atom.relation = parseRelation)
    (childArguments : termsToList atom.arguments = [child, input, value, output])
    (parentGround : (encodeScopedTerm .query parentGrammar).isGround)
    (candidate : Mettapedia.Logic.LP.Subst compilerSignature)
    (unifies : candidate.applyAtom
        (encodeScopedAtom .query (parserQuery parseRelation parentGrammar)) =
      candidate.applyAtom (encodeScopedAtom .rule rule.head)) :
    candidate.applyTerm (encodeScopedTerm .rule child) =
      headMatch.substitution.applyTerm (encodeScopedTerm .rule child) := by
  have decoded := safeTotalMatchedChild_is_decoded matched headRelation
    headArguments safe member childRelation childArguments parentGround
  have ground : (headMatch.substitution.applyTerm
      (encodeScopedTerm .rule child)).isGround := by
    unfold instantiatedChildGrammarTotal at decoded
    split at decoded
    next mismatch => simp at decoded
    next relationMatch =>
      rw [childArguments] at decoded
      exact decodeGroundCompilerTerm_isGround decoded
  exact matched.factorGroundTerm candidate unifies
    (encodeScopedTerm .rule child) ground

def discoverProgramRootCategoryTableTotal (program : Program)
    (parseRelation : String) (closureFuel : Nat) (root : Term) :
    Option HornReachableClosure.DiscoveredRootTable :=
  if parserProgramSafe program parseRelation then
    HornReachableClosure.discoverRootCategoryTable root
      (programChildrenTotal program parseRelation) closureFuel
  else none

theorem discoverProgramRootCategoryTableTotal_program_safe
    {program : Program} {parseRelation : String} {closureFuel : Nat}
    {root : Term} {result : HornReachableClosure.DiscoveredRootTable}
    (accepted : discoverProgramRootCategoryTableTotal program parseRelation
      closureFuel root = some result) :
    parserProgramSafe program parseRelation = true := by
  simp only [discoverProgramRootCategoryTableTotal] at accepted
  split at accepted
  next safe => exact safe
  next notSafe => simp at accepted

theorem discoverProgramRootCategoryTableTotal_domain_exact
    {program : Program} {parseRelation : String} {closureFuel : Nat}
    {root grammar : Term} {result : HornReachableClosure.DiscoveredRootTable}
    (accepted : discoverProgramRootCategoryTableTotal program parseRelation
      closureFuel root = some result) :
    grammar ∈ result.domain ↔
      HornRootUniverse.Reachable root
        (programChildrenTotal program parseRelation) grammar := by
  have safe := discoverProgramRootCategoryTableTotal_program_safe accepted
  exact HornReachableClosure.discoverRootCategoryTable_domain_exact
    (result := result) (root := root)
    (children := programChildrenTotal program parseRelation)
    (fuel := closureFuel)
    (by simpa [discoverProgramRootCategoryTableTotal, safe] using accepted)

theorem discoverProgramRootCategoryTableTotal_category_exact
    {program : Program} {parseRelation : String} {closureFuel : Nat}
    {root grammar : Term} {result : HornReachableClosure.DiscoveredRootTable}
    (accepted : discoverProgramRootCategoryTableTotal program parseRelation
      closureFuel root = some result) :
    (∃ category, lookupCategory grammar result.table = some category) ↔
      HornRootUniverse.Reachable root
        (programChildrenTotal program parseRelation) grammar := by
  have safe := discoverProgramRootCategoryTableTotal_program_safe accepted
  exact HornReachableClosure.discoverRootCategoryTable_category_exact
    (result := result) (root := root)
    (children := programChildrenTotal program parseRelation)
    (fuel := closureFuel)
    (by simpa [discoverProgramRootCategoryTableTotal, safe] using accepted)

def discoverProgramRootCategoryTable (program : Program) (parseRelation : String)
    (unificationFuel closureFuel : Nat) (root : Term) :
    Option HornReachableClosure.DiscoveredRootTable :=
  if parserProgramSafe program parseRelation then
    HornReachableClosure.discoverRootCategoryTable root
      (programChildren program parseRelation unificationFuel) closureFuel
  else none

theorem discoverProgramRootCategoryTable_program_safe
    {program : Program} {parseRelation : String}
    {unificationFuel closureFuel : Nat} {root : Term}
    {result : HornReachableClosure.DiscoveredRootTable}
    (accepted : discoverProgramRootCategoryTable program parseRelation
      unificationFuel closureFuel root = some result) :
    parserProgramSafe program parseRelation = true := by
  simp only [discoverProgramRootCategoryTable] at accepted
  split at accepted
  next safe => exact safe
  next notSafe => simp at accepted

theorem discoverProgramRootCategoryTable_domain_exact
    {program : Program} {parseRelation : String}
    {unificationFuel closureFuel : Nat} {root grammar : Term}
    {result : HornReachableClosure.DiscoveredRootTable}
    (accepted : discoverProgramRootCategoryTable program parseRelation
      unificationFuel closureFuel root = some result) :
    grammar ∈ result.domain ↔
      HornRootUniverse.Reachable root
        (programChildren program parseRelation unificationFuel) grammar := by
  have safe := discoverProgramRootCategoryTable_program_safe accepted
  simpa [discoverProgramRootCategoryTable, safe] using
    (HornReachableClosure.discoverRootCategoryTable_domain_exact
      (result := result) (root := root)
      (children := programChildren program parseRelation unificationFuel)
      (fuel := closureFuel)
      (by simpa [discoverProgramRootCategoryTable, safe] using accepted))

theorem discoverProgramRootCategoryTable_category_exact
    {program : Program} {parseRelation : String}
    {unificationFuel closureFuel : Nat} {root grammar : Term}
    {result : HornReachableClosure.DiscoveredRootTable}
    (accepted : discoverProgramRootCategoryTable program parseRelation
      unificationFuel closureFuel root = some result) :
    (∃ category, lookupCategory grammar result.table = some category) ↔
      HornRootUniverse.Reachable root
        (programChildren program parseRelation unificationFuel) grammar := by
  have safe := discoverProgramRootCategoryTable_program_safe accepted
  exact HornReachableClosure.discoverRootCategoryTable_category_exact
    (result := result) (root := root)
    (children := programChildren program parseRelation unificationFuel)
    (fuel := closureFuel)
    (by simpa [discoverProgramRootCategoryTable, safe] using accepted)

/-! ## Executable positive and negative controls -/

def rootGrammar : Term := .app "root" .nil
def childGrammar : Term := .app "child" .nil

def recursiveRule : Rule :=
  { name := "recursive"
    head :=
      { relation := "parse"
        arguments := Terms.ofList [rootGrammar, .var 0, .var 1, .var 2] }
    body :=
      [{ relation := "parse"
         arguments := Terms.ofList [childGrammar, .var 0, .var 1, .var 2] }] }

def leafRule : Rule :=
  { name := "leaf"
    head :=
      { relation := "parse"
        arguments := Terms.ofList [childGrammar, .var 0, .var 1, .var 2] }
    body := [] }

def recursiveProgram : Program := [recursiveRule, leafRule]

private theorem recursiveRule_semantically_unifiable :
    SemanticallyUnifiable (parserQuery "parse" rootGrammar) recursiveRule := by
  cases accepted : matchHead (parserQuery "parse" rootGrammar) 100
      recursiveRule with
  | none =>
      have nonempty :
          (matchHead (parserQuery "parse" rootGrammar) 100
            recursiveRule).isSome = true := by
        decide
      simp [accepted] at nonempty
  | some headMatch =>
      exact ⟨headMatch.substitution,
        (matchHead_sound (parserQuery "parse" rootGrammar) 100
          recursiveRule headMatch accepted).sound.2.2⟩

private theorem leafRule_not_semantically_unifiable :
    ¬SemanticallyUnifiable (parserQuery "parse" rootGrammar) leafRule := by
  rintro ⟨substitution, equal⟩
  have argumentEquality := congrArg compilerAtomArguments equal
  simp [compilerAtomArguments, Mettapedia.Logic.LP.Subst.applyAtom,
    parserQuery, leafRule, rootGrammar, childGrammar, encodeScopedAtom,
    encodeScopedTerms, encodeScopedTerm, Terms.ofList] at argumentEquality

private theorem recursiveRule_not_semantically_unifiable_at_child :
    ¬SemanticallyUnifiable (parserQuery "parse" childGrammar)
      recursiveRule := by
  rintro ⟨substitution, equal⟩
  have argumentEquality := congrArg compilerAtomArguments equal
  simp [compilerAtomArguments, Mettapedia.Logic.LP.Subst.applyAtom,
    parserQuery, recursiveRule, rootGrammar, childGrammar, encodeScopedAtom,
    encodeScopedTerms, encodeScopedTerm, Terms.ofList] at argumentEquality

private theorem leafRule_semantically_unifiable_at_child :
    SemanticallyUnifiable (parserQuery "parse" childGrammar) leafRule := by
  cases accepted : matchHead (parserQuery "parse" childGrammar) 100 leafRule with
  | none =>
      have nonempty :
          (matchHead (parserQuery "parse" childGrammar) 100 leafRule).isSome =
            true := by
        decide
      simp [accepted] at nonempty
  | some headMatch =>
      exact ⟨headMatch.substitution,
        (matchHead_sound (parserQuery "parse" childGrammar) 100 leafRule
          headMatch accepted).sound.2.2⟩

theorem recursive_program_discovers_child :
    programChildren recursiveProgram "parse" 100 rootGrammar = [childGrammar] := by
  cases accepted : matchHead (parserQuery "parse" rootGrammar) 100
      recursiveRule with
  | none =>
      have nonempty :
          (matchHead (parserQuery "parse" rootGrammar) 100
            recursiveRule).isSome = true := by
        decide
      simp [accepted] at nonempty
  | some headMatch =>
      have leafRejected :
          matchHead (parserQuery "parse" rootGrammar) 100 leafRule = none := by
        decide
      have matched := matchHead_sound (parserQuery "parse" rootGrammar) 100
        recursiveRule headMatch accepted
      have ruleEq : headMatch.rule = recursiveRule := matched.sound.1
      have childGround :
          (encodeScopedTerm .rule childGrammar).isGround := by
        simp [childGrammar, encodeScopedTerm,
          encodeScopedTerms,
          Mettapedia.Logic.LP.Term.isGround]
      have decoded :=
        decodeGroundCompilerTerm_apply_encodeScopedTerm_of_ground
          headMatch.substitution .rule childGrammar childGround
      simp only [programChildren, matchHeads, recursiveProgram,
        List.filterMap_cons, accepted, leafRejected, List.filterMap_nil,
        List.flatMap_cons, List.flatMap_nil]
      simp only [matchedChildren]
      rw [ruleEq]
      simp [recursiveRule, instantiatedChildGrammar, termsToList,
        Terms.ofList, decoded]

theorem zero_unification_fuel_misses_real_child :
    programChildren recursiveProgram "parse" 0 rootGrammar = [] := by
  decide

private theorem recursive_program_child_has_no_children :
    programChildren recursiveProgram "parse" 100 childGrammar = [] := by
  decide

private theorem total_recursive_program_child_has_no_children :
    programChildrenTotal recursiveProgram "parse" childGrammar = [] := by
  obtain ⟨substitution, leafAccepted⟩ :=
    unifyApartTotal_complete (parserQuery "parse" childGrammar) leafRule.head
      leafRule_semantically_unifiable_at_child
  let leafMatch : TotalHeadMatch := { rule := leafRule, substitution }
  have leafMatchAccepted :
      matchHeadTotal (parserQuery "parse" childGrammar) leafRule =
        some leafMatch := by
    simp [matchHeadTotal, leafAccepted, leafMatch]
  have recursiveUnificationRejected :
      unifyApartTotal (parserQuery "parse" childGrammar) recursiveRule.head =
        none :=
    (unifyApartTotal_none_iff_not_unifiable _ _).mpr
      recursiveRule_not_semantically_unifiable_at_child
  have recursiveRejected :
      matchHeadTotal (parserQuery "parse" childGrammar) recursiveRule = none := by
    simp [matchHeadTotal, recursiveUnificationRejected]
  simp only [programChildrenTotal, matchHeadsTotal, recursiveProgram,
    List.filterMap_cons, recursiveRejected, leafMatchAccepted,
    List.filterMap_nil, List.flatMap_cons, List.flatMap_nil]
  simp [leafMatch, matchedChildrenTotal, leafRule]

theorem total_recursive_program_discovers_child :
    programChildrenTotal recursiveProgram "parse" rootGrammar =
      [childGrammar] := by
  obtain ⟨substitution, totalAccepted⟩ :=
    unifyApartTotal_complete (parserQuery "parse" rootGrammar)
      recursiveRule.head recursiveRule_semantically_unifiable
  let headMatch : TotalHeadMatch := { rule := recursiveRule, substitution }
  have recursiveAccepted :
      matchHeadTotal (parserQuery "parse" rootGrammar) recursiveRule =
        some headMatch := by
    simp [matchHeadTotal, totalAccepted, headMatch]
  have leafUnificationRejected :
      unifyApartTotal (parserQuery "parse" rootGrammar) leafRule.head = none :=
    (unifyApartTotal_none_iff_not_unifiable _ _).mpr
      leafRule_not_semantically_unifiable
  have leafRejected :
      matchHeadTotal (parserQuery "parse" rootGrammar) leafRule = none := by
    simp [matchHeadTotal, leafUnificationRejected]
  have childGround :
      (encodeScopedTerm .rule childGrammar).isGround := by
    simp [childGrammar, encodeScopedTerm, encodeScopedTerms,
      Mettapedia.Logic.LP.Term.isGround]
  have decoded :=
    decodeGroundCompilerTerm_apply_encodeScopedTerm_of_ground
      substitution .rule childGrammar childGround
  simp only [programChildrenTotal, matchHeadsTotal, recursiveProgram,
    List.filterMap_cons, recursiveAccepted, leafRejected,
    List.filterMap_nil, List.flatMap_cons, List.flatMap_nil]
  simp [headMatch, matchedChildrenTotal, recursiveRule,
    instantiatedChildGrammarTotal, termsToList, Terms.ofList, decoded]

private theorem recursive_program_discovered_domain :
    HornReachableClosure.discoverDomain rootGrammar
        (programChildren recursiveProgram "parse" 100) 1 =
      [rootGrammar, childGrammar] := by
  simp only [HornReachableClosure.discoverDomain,
    HornReachableClosure.expandDomain, List.flatMap_cons, List.flatMap_nil,
    recursive_program_discovers_child]
  simp [rootGrammar, childGrammar]

private theorem total_recursive_program_discovered_domain :
    HornReachableClosure.discoverDomain rootGrammar
        (programChildrenTotal recursiveProgram "parse") 1 =
      [rootGrammar, childGrammar] := by
  simp only [HornReachableClosure.discoverDomain,
    HornReachableClosure.expandDomain, List.flatMap_cons, List.flatMap_nil,
    total_recursive_program_discovers_child]
  simp [rootGrammar, childGrammar]

private theorem recursive_program_root_universe_covers :
    HornRootUniverse.RootUniverseCovers rootGrammar
      (programChildren recursiveProgram "parse" 100)
      [rootGrammar, childGrammar] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [rootGrammar, childGrammar]
  · simp
  · intro grammar member
    simp at member
    rcases member with rfl | rfl <;>
      simp [rootGrammar, childGrammar, termVariables, termsVariables]
  · intro grammar member child childMember
    simp at member
    rcases member with rfl | rfl
    · rw [recursive_program_discovers_child] at childMember
      simp at childMember
      simp [childMember]
    · rw [recursive_program_child_has_no_children] at childMember
      simp at childMember

private theorem total_recursive_program_root_universe_covers :
    HornRootUniverse.RootUniverseCovers rootGrammar
      (programChildrenTotal recursiveProgram "parse")
      [rootGrammar, childGrammar] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [rootGrammar, childGrammar]
  · simp
  · intro grammar member
    simp at member
    rcases member with rfl | rfl <;>
      simp [rootGrammar, childGrammar, termVariables, termsVariables]
  · intro grammar member child childMember
    simp at member
    rcases member with rfl | rfl
    · rw [total_recursive_program_discovers_child] at childMember
      simp at childMember
      simp [childMember]
    · rw [total_recursive_program_child_has_no_children] at childMember
      simp at childMember

theorem recursive_program_constructs_closed_root_table :
    (discoverProgramRootCategoryTable recursiveProgram "parse" 100 1
      rootGrammar).isSome = true := by
  have safe : parserProgramSafe recursiveProgram "parse" = true := by
    decide
  have universeValid :
      HornRootUniverse.rootUniverseValid rootGrammar
          (programChildren recursiveProgram "parse" 100)
          [rootGrammar, childGrammar] = true :=
    (HornRootUniverse.rootUniverseValid_iff _ _ _).mpr
      recursive_program_root_universe_covers
  have tableAccepted :
      HornRootUniverse.buildRootCategoryTable rootGrammar
          (programChildren recursiveProgram "parse" 100)
          [rootGrammar, childGrammar] =
        some (HornCategoryTable.makeCategoryTable
          [rootGrammar, childGrammar]) := by
    simp [HornRootUniverse.buildRootCategoryTable, universeValid]
  unfold discoverProgramRootCategoryTable
  rw [if_pos safe]
  unfold HornReachableClosure.discoverRootCategoryTable
  rw [recursive_program_discovered_domain]
  simp [tableAccepted]

theorem total_recursive_program_constructs_closed_root_table :
    (discoverProgramRootCategoryTableTotal recursiveProgram "parse" 1
      rootGrammar).isSome = true := by
  have safe : parserProgramSafe recursiveProgram "parse" = true := by
    decide
  have universeValid :
      HornRootUniverse.rootUniverseValid rootGrammar
          (programChildrenTotal recursiveProgram "parse")
          [rootGrammar, childGrammar] = true :=
    (HornRootUniverse.rootUniverseValid_iff _ _ _).mpr
      total_recursive_program_root_universe_covers
  have tableAccepted :
      HornRootUniverse.buildRootCategoryTable rootGrammar
          (programChildrenTotal recursiveProgram "parse")
          [rootGrammar, childGrammar] =
        some (HornCategoryTable.makeCategoryTable
          [rootGrammar, childGrammar]) := by
    simp [HornRootUniverse.buildRootCategoryTable, universeValid]
  unfold discoverProgramRootCategoryTableTotal
  rw [if_pos safe]
  unfold HornReachableClosure.discoverRootCategoryTable
  rw [total_recursive_program_discovered_domain]
  simp [tableAccepted]

def unsafeResidualChildRule : Rule :=
  { recursiveRule with
    name := "unsafe-residual-child"
    body :=
      [{ relation := "parse"
         arguments := Terms.ofList [.var 99, .var 0, .var 1, .var 2] }] }

theorem residual_symbolic_child_is_rejected :
    programChildren [unsafeResidualChildRule] "parse" 100 rootGrammar = [] := by
  decide

theorem residual_symbolic_child_rule_is_unsafe :
    parserProgramSafe [unsafeResidualChildRule] "parse" = false := by
  decide

theorem residual_symbolic_child_program_is_not_admitted :
    discoverProgramRootCategoryTable [unsafeResidualChildRule] "parse" 100 0
      rootGrammar = none := by
  decide

theorem total_residual_symbolic_child_program_is_not_admitted :
    discoverProgramRootCategoryTableTotal [unsafeResidualChildRule] "parse" 0
      rootGrammar = none := by
  decide

def malformedParserRule : Rule :=
  { name := "malformed-parser-arity"
    head := { relation := "parse", arguments := Terms.ofList [rootGrammar] }
    body := [] }

theorem malformed_parser_arity_is_not_admitted :
    parserProgramSafe [malformedParserRule] "parse" = false := by
  decide

theorem wrong_relation_has_no_children :
    programChildren recursiveProgram "not-parse" 100 rootGrammar = [] := by
  decide

end Mettapedia.GSLT.Parsing.HornProgramChildren
