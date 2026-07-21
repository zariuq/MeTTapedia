import Mettapedia.GSLT.Parsing.HornUnification

/-!
# Exhaustive Horn-rule head enumeration

The syntax-GSLT compiler must discover applicable source rules from the
admitted program rather than receive a hand-authored request list.  This
module scans every admitted rule with apart-renamed, occurs-checked
unification.  It proves exactness at a checked fuel bound and proves that a
single finite bound exists for every semantically unifiable head in a finite
program.

This is head-enumeration correspondence.  Turning each match into a complete
`SpecializationCertificate`, including side-premise certificates and category
discovery, remains the subsequent compiler-reflection step.
-/

namespace Mettapedia.GSLT.Parsing.HornHeadEnumeration

open HornCertificate HornUnification

structure HeadMatch where
  rule : Rule
  fuel : Nat
  substitution : Mettapedia.Logic.LP.Subst compilerSignature

def matchHead (query : Atom) (maximumFuel : Nat) (rule : Rule) :
    Option HeadMatch := do
  let (fuel, substitution) ← firstUnifier query rule.head maximumFuel
  pure { rule, fuel, substitution }

inductive HeadMatches (query : Atom) (maximumFuel : Nat) :
    Rule → HeadMatch → Prop where
  | intro (rule : Rule) (fuel : Nat)
      (substitution : Mettapedia.Logic.LP.Subst compilerSignature)
      (accepted : firstUnifier query rule.head maximumFuel =
        some (fuel, substitution)) :
      HeadMatches query maximumFuel rule { rule, fuel, substitution }

theorem matchHead_sound (query : Atom) (maximumFuel : Nat)
    (rule : Rule) (result : HeadMatch)
    (accepted : matchHead query maximumFuel rule = some result) :
    HeadMatches query maximumFuel rule result := by
  cases found : firstUnifier query rule.head maximumFuel with
  | none => simp [matchHead, found] at accepted
  | some pair =>
      obtain ⟨fuel, substitution⟩ := pair
      simp [matchHead, found] at accepted
      subst result
      exact .intro rule fuel substitution found

theorem matchHead_complete (query : Atom) (maximumFuel : Nat)
    (rule : Rule) (result : HeadMatch)
    (matched : HeadMatches query maximumFuel rule result) :
    matchHead query maximumFuel rule = some result := by
  cases matched with
  | intro fuel substitution accepted =>
      simp [matchHead, accepted]

theorem matchHead_iff (query : Atom) (maximumFuel : Nat)
    (rule : Rule) (result : HeadMatch) :
    matchHead query maximumFuel rule = some result ↔
      HeadMatches query maximumFuel rule result :=
  ⟨matchHead_sound query maximumFuel rule result,
    matchHead_complete query maximumFuel rule result⟩

theorem HeadMatches.sound {query : Atom} {maximumFuel : Nat}
    {rule : Rule} {result : HeadMatch}
    (matched : HeadMatches query maximumFuel rule result) :
    result.rule = rule ∧ result.fuel ≤ maximumFuel ∧
      result.substitution.applyAtom (encodeScopedAtom .query query) =
        result.substitution.applyAtom (encodeScopedAtom .rule rule.head) := by
  cases matched with
  | intro fuel substitution accepted =>
      obtain ⟨within, unifierAccepted⟩ :=
        firstUnifier_sound query rule.head maximumFuel fuel substitution accepted
      exact ⟨rfl, within,
        unifyApart_sound query rule.head fuel substitution unifierAccepted⟩

/-- The substitution selected by an executable head match is a most-general
unifier.  Any semantic specialization unifier therefore factors through the
compiler's chosen substitution. -/
theorem HeadMatches.mostGeneral {query : Atom} {maximumFuel : Nat}
    {rule : Rule} {result : HeadMatch}
    (matched : HeadMatches query maximumFuel rule result)
    (candidate : Mettapedia.Logic.LP.Subst compilerSignature)
    (unifies :
      candidate.applyAtom (encodeScopedAtom .query query) =
        candidate.applyAtom (encodeScopedAtom .rule rule.head)) :
  result.substitution.moreGeneral candidate := by
  cases matched with
  | intro fuel substitution accepted =>
      obtain ⟨_, unifierAccepted⟩ :=
        firstUnifier_sound query rule.head maximumFuel fuel substitution accepted
      exact Mettapedia.Logic.LP.unifyAtoms_mgu
        (encodeScopedAtom .query query) (encodeScopedAtom .rule rule.head)
        fuel substitution (by simpa [unifyApart] using unifierAccepted)
        candidate unifies

theorem HeadMatches.factorTerm {query : Atom} {maximumFuel : Nat}
    {rule : Rule} {result : HeadMatch}
    (matched : HeadMatches query maximumFuel rule result)
    (candidate : Mettapedia.Logic.LP.Subst compilerSignature)
    (unifies :
      candidate.applyAtom (encodeScopedAtom .query query) =
        candidate.applyAtom (encodeScopedAtom .rule rule.head))
    (term : Mettapedia.Logic.LP.Term compilerSignature) :
    ∃ residual : Mettapedia.Logic.LP.Subst compilerSignature,
      candidate.applyTerm term =
        residual.applyTerm (result.substitution.applyTerm term) := by
  obtain ⟨residual, factors⟩ := matched.mostGeneral candidate unifies
  refine ⟨residual, ?_⟩
  induction term with
  | var v => exact factors v
  | const c => rfl
  | app f ts ih =>
      simp only [Mettapedia.Logic.LP.Subst.applyTerm]
      congr
      funext i
      exact ih i

theorem applyTerm_eq_self_of_isGround
    (substitution : Mettapedia.Logic.LP.Subst compilerSignature)
    {term : Mettapedia.Logic.LP.Term compilerSignature}
    (ground : term.isGround) :
    substitution.applyTerm term = term := by
  induction term with
  | var v => simp [Mettapedia.Logic.LP.Term.isGround] at ground
  | const c => rfl
  | app f ts ih =>
      simp only [Mettapedia.Logic.LP.Subst.applyTerm]
      congr
      funext i
      exact ih i (ground i)

theorem applyTerm_ground_iff_variables_ground
    (substitution : Mettapedia.Logic.LP.Subst compilerSignature)
    (term : Mettapedia.Logic.LP.Term compilerSignature) :
    (substitution.applyTerm term).isGround ↔
      ∀ v ∈ term.freeVars, (substitution v).isGround := by
  induction term with
  | var v =>
      simp [Mettapedia.Logic.LP.Subst.applyTerm,
        Mettapedia.Logic.LP.Term.freeVars]
  | const c =>
      simp [Mettapedia.Logic.LP.Subst.applyTerm,
        Mettapedia.Logic.LP.Term.isGround,
        Mettapedia.Logic.LP.Term.freeVars]
  | app f ts ih =>
      simp only [Mettapedia.Logic.LP.Subst.applyTerm,
        Mettapedia.Logic.LP.Term.isGround,
        Mettapedia.Logic.LP.Term.freeVars,
        Finset.mem_biUnion, Finset.mem_univ, true_and,
        ih]
      constructor
      · intro ground v member
        obtain ⟨i, member⟩ := member
        exact ground i v member
      · intro ground i v member
        exact ground v ⟨i, member⟩

theorem applyTerm_ground_of_freeVars_subset
    (substitution : Mettapedia.Logic.LP.Subst compilerSignature)
    {source target : Mettapedia.Logic.LP.Term compilerSignature}
    (subset : source.freeVars ⊆ target.freeVars)
    (targetGround : (substitution.applyTerm target).isGround) :
    (substitution.applyTerm source).isGround := by
  rw [applyTerm_ground_iff_variables_ground substitution target] at targetGround
  rw [applyTerm_ground_iff_variables_ground substitution source]
  intro v member
  exact targetGround v (subset member)

/-- Once the compiler's MGU makes a source term ground, every more-specific
semantic unifier gives exactly the same instantiated term. -/
theorem HeadMatches.factorGroundTerm {query : Atom} {maximumFuel : Nat}
    {rule : Rule} {result : HeadMatch}
    (matched : HeadMatches query maximumFuel rule result)
    (candidate : Mettapedia.Logic.LP.Subst compilerSignature)
    (unifies :
      candidate.applyAtom (encodeScopedAtom .query query) =
        candidate.applyAtom (encodeScopedAtom .rule rule.head))
    (term : Mettapedia.Logic.LP.Term compilerSignature)
    (ground : (result.substitution.applyTerm term).isGround) :
    candidate.applyTerm term = result.substitution.applyTerm term := by
  obtain ⟨residual, factor⟩ := matched.factorTerm candidate unifies term
  rw [factor, applyTerm_eq_self_of_isGround residual ground]

def matchHeads (program : Program) (query : Atom)
    (maximumFuel : Nat) : List HeadMatch :=
  program.filterMap (matchHead query maximumFuel)

theorem matchHeads_sound (program : Program) (query : Atom)
    (maximumFuel : Nat) (result : HeadMatch)
    (member : result ∈ matchHeads program query maximumFuel) :
    ∃ rule ∈ program, HeadMatches query maximumFuel rule result := by
  rw [matchHeads, List.mem_filterMap] at member
  obtain ⟨rule, ruleMember, accepted⟩ := member
  exact ⟨rule, ruleMember,
    matchHead_sound query maximumFuel rule result accepted⟩

theorem matchHeads_complete (program : Program) (query : Atom)
    (maximumFuel : Nat) (rule : Rule) (result : HeadMatch)
    (ruleMember : rule ∈ program)
    (matched : HeadMatches query maximumFuel rule result) :
    result ∈ matchHeads program query maximumFuel := by
  rw [matchHeads, List.mem_filterMap]
  exact ⟨rule, ruleMember,
    matchHead_complete query maximumFuel rule result matched⟩

theorem matchHeads_iff (program : Program) (query : Atom)
    (maximumFuel : Nat) (result : HeadMatch) :
    result ∈ matchHeads program query maximumFuel ↔
      ∃ rule ∈ program, HeadMatches query maximumFuel rule result := by
  constructor
  · exact matchHeads_sound program query maximumFuel result
  · rintro ⟨rule, member, matched⟩
    exact matchHeads_complete program query maximumFuel rule result member matched

theorem matchHeads_every_result_is_source_derived
    (program : Program) (query : Atom) (maximumFuel : Nat)
    (result : HeadMatch)
    (member : result ∈ matchHeads program query maximumFuel) :
    result.rule ∈ program ∧ result.fuel ≤ maximumFuel ∧
      result.substitution.applyAtom (encodeScopedAtom .query query) =
        result.substitution.applyAtom
          (encodeScopedAtom .rule result.rule.head) := by
  obtain ⟨rule, ruleMember, matched⟩ :=
    matchHeads_sound program query maximumFuel result member
  obtain ⟨ruleEq, within, unifies⟩ := matched.sound
  subst rule
  exact ⟨ruleMember, within, unifies⟩

def SemanticallyUnifiable (query : Atom) (rule : Rule) : Prop :=
  ∃ substitution : Mettapedia.Logic.LP.Subst compilerSignature,
    substitution.applyAtom (encodeScopedAtom .query query) =
      substitution.applyAtom (encodeScopedAtom .rule rule.head)

/-! ## Total head enumeration

The bounded enumerator remains useful as an explicit `Incomplete` reference
path.  Admission and production compilation use this fuel-free sibling so a
missing head is a proved mismatch rather than an exhausted search. -/

structure TotalHeadMatch where
  rule : Rule
  substitution : Mettapedia.Logic.LP.Subst compilerSignature

def matchHeadTotal (query : Atom) (rule : Rule) : Option TotalHeadMatch := do
  let substitution ← unifyApartTotal query rule.head
  pure { rule, substitution }

inductive TotalHeadMatches (query : Atom) : Rule → TotalHeadMatch → Prop where
  | intro (rule : Rule)
      (substitution : Mettapedia.Logic.LP.Subst compilerSignature)
      (accepted : unifyApartTotal query rule.head = some substitution) :
      TotalHeadMatches query rule { rule, substitution }

theorem matchHeadTotal_iff (query : Atom) (rule : Rule)
    (result : TotalHeadMatch) :
    matchHeadTotal query rule = some result ↔
      TotalHeadMatches query rule result := by
  constructor
  · intro accepted
    cases found : unifyApartTotal query rule.head with
    | none => simp [matchHeadTotal, found] at accepted
    | some substitution =>
        simp [matchHeadTotal, found] at accepted
        subst result
        exact .intro rule substitution found
  · intro matched
    cases matched with
    | intro substitution accepted => simp [matchHeadTotal, accepted]

theorem TotalHeadMatches.sound {query : Atom} {rule : Rule}
    {result : TotalHeadMatch} (matched : TotalHeadMatches query rule result) :
    result.rule = rule ∧
      result.substitution.applyAtom (encodeScopedAtom .query query) =
        result.substitution.applyAtom (encodeScopedAtom .rule rule.head) := by
  cases matched with
  | intro substitution accepted =>
      exact ⟨rfl, unifyApartTotal_sound query rule.head substitution accepted⟩

theorem TotalHeadMatches.mostGeneral {query : Atom} {rule : Rule}
    {result : TotalHeadMatch} (matched : TotalHeadMatches query rule result)
    (candidate : Mettapedia.Logic.LP.Subst compilerSignature)
    (unifies : candidate.applyAtom (encodeScopedAtom .query query) =
      candidate.applyAtom (encodeScopedAtom .rule rule.head)) :
    result.substitution.moreGeneral candidate := by
  cases matched with
  | intro substitution accepted =>
      exact unifyApartTotal_mgu query rule.head substitution accepted candidate
        unifies

theorem TotalHeadMatches.factorGroundTerm {query : Atom} {rule : Rule}
    {result : TotalHeadMatch} (matched : TotalHeadMatches query rule result)
    (candidate : Mettapedia.Logic.LP.Subst compilerSignature)
    (unifies : candidate.applyAtom (encodeScopedAtom .query query) =
      candidate.applyAtom (encodeScopedAtom .rule rule.head))
    (term : Mettapedia.Logic.LP.Term compilerSignature)
    (ground : (result.substitution.applyTerm term).isGround) :
    candidate.applyTerm term = result.substitution.applyTerm term := by
  obtain ⟨residual, factors⟩ := matched.mostGeneral candidate unifies
  have factor : candidate.applyTerm term =
      residual.applyTerm (result.substitution.applyTerm term) := by
    induction term with
    | var v => exact factors v
    | const c => rfl
    | app function arguments inductionHypothesis =>
        simp only [Mettapedia.Logic.LP.Subst.applyTerm]
        congr
        funext index
        exact inductionHypothesis index (ground index)
  rw [factor, applyTerm_eq_self_of_isGround residual ground]

def matchHeadsTotal (program : Program) (query : Atom) : List TotalHeadMatch :=
  program.filterMap (matchHeadTotal query)

theorem mem_matchHeadsTotal_iff
    {program : Program} {query : Atom} {result : TotalHeadMatch} :
    result ∈ matchHeadsTotal program query ↔
      ∃ rule ∈ program, TotalHeadMatches query rule result := by
  rw [matchHeadsTotal, List.mem_filterMap]
  constructor
  · rintro ⟨rule, member, accepted⟩
    exact ⟨rule, member, (matchHeadTotal_iff query rule result).mp accepted⟩
  · rintro ⟨rule, member, matched⟩
    exact ⟨rule, member, (matchHeadTotal_iff query rule result).mpr matched⟩

theorem matchHeadsTotal_every_result_is_source_derived
    {program : Program} {query : Atom} {result : TotalHeadMatch}
    (member : result ∈ matchHeadsTotal program query) :
    result.rule ∈ program ∧
      result.substitution.applyAtom (encodeScopedAtom .query query) =
        result.substitution.applyAtom
          (encodeScopedAtom .rule result.rule.head) := by
  obtain ⟨rule, ruleMember, matched⟩ := mem_matchHeadsTotal_iff.mp member
  obtain ⟨ruleEq, unifies⟩ := matched.sound
  subst rule
  exact ⟨ruleMember, unifies⟩

theorem matchHeadsTotal_semantically_exhaustive
    (program : Program) (query : Atom) (rule : Rule)
    (ruleMember : rule ∈ program)
    (unifiable : SemanticallyUnifiable query rule) :
    ∃ result ∈ matchHeadsTotal program query,
      TotalHeadMatches query rule result := by
  obtain ⟨substitution, accepted⟩ :=
    unifyApartTotal_complete query rule.head unifiable
  let result : TotalHeadMatch := { rule, substitution }
  have matched : TotalHeadMatches query rule result :=
    .intro rule substitution accepted
  exact ⟨result, mem_matchHeadsTotal_iff.mpr
    ⟨rule, ruleMember, matched⟩, matched⟩

theorem matchHeadsTotal_none_iff_no_semantic_match
    (program : Program) (query : Atom) :
    matchHeadsTotal program query = [] ↔
      ∀ rule ∈ program, ¬SemanticallyUnifiable query rule := by
  constructor
  · intro empty rule member unifiable
    obtain ⟨result, resultMember, matched⟩ :=
      matchHeadsTotal_semantically_exhaustive program query rule member unifiable
    rw [empty] at resultMember
    simp at resultMember
  · intro noMatch
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro result resultMember
    obtain ⟨rule, ruleMember, matched⟩ :=
      mem_matchHeadsTotal_iff.mp resultMember
    exact noMatch rule ruleMember ⟨result.substitution, matched.sound.2⟩

def AllUnifiersBounded (program : Program) (query : Atom)
    (maximumFuel : Nat) : Prop :=
  ∀ rule ∈ program, SemanticallyUnifiable query rule →
    ∃ fuel substitution, fuel ≤ maximumFuel ∧
      unifyApart query rule.head fuel = some substitution

theorem finiteProgram_has_unification_bound (program : Program) (query : Atom) :
    ∃ maximumFuel, AllUnifiersBounded program query maximumFuel := by
  induction program with
  | nil =>
      exact ⟨0, by simp [AllUnifiersBounded]⟩
  | cons rule rules inductionHypothesis =>
      obtain ⟨tailMaximum, tailBounded⟩ := inductionHypothesis
      classical
      by_cases unifiable : SemanticallyUnifiable query rule
      · obtain ⟨ruleFuel, substitution, accepted⟩ :=
          unifyApart_complete query rule.head unifiable
        refine ⟨max tailMaximum ruleFuel, ?_⟩
        intro candidate member candidateUnifiable
        simp only [List.mem_cons] at member
        rcases member with rfl | tailMember
        · exact ⟨ruleFuel, substitution, Nat.le_max_right _ _, accepted⟩
        · obtain ⟨fuel, tailSubstitution, bounded, tailAccepted⟩ :=
            tailBounded candidate tailMember candidateUnifiable
          exact ⟨fuel, tailSubstitution,
            Nat.le_trans bounded (Nat.le_max_left _ _), tailAccepted⟩
      · exact ⟨tailMaximum, by
          intro candidate member candidateUnifiable
          simp only [List.mem_cons] at member
          rcases member with rfl | tailMember
          · exact False.elim (unifiable candidateUnifiable)
          · exact tailBounded candidate tailMember candidateUnifiable⟩

theorem matchHeads_semantically_exhaustive
    (program : Program) (query : Atom) (maximumFuel : Nat)
    (bounded : AllUnifiersBounded program query maximumFuel)
    (rule : Rule) (ruleMember : rule ∈ program)
    (unifiable : SemanticallyUnifiable query rule) :
    ∃ result ∈ matchHeads program query maximumFuel,
      HeadMatches query maximumFuel rule result := by
  obtain ⟨fuel, substitution, within, accepted⟩ :=
    bounded rule ruleMember unifiable
  have found := firstUnifier_complete query rule.head maximumFuel fuel
    substitution within accepted
  cases result : firstUnifier query rule.head maximumFuel with
  | none => simp [result] at found
  | some pair =>
      obtain ⟨foundFuel, foundSubstitution⟩ := pair
      let headMatch : HeadMatch :=
        { rule := rule
          fuel := foundFuel
          substitution := foundSubstitution }
      have matched : HeadMatches query maximumFuel rule headMatch := by
        exact .intro rule foundFuel foundSubstitution result
      exact ⟨headMatch,
        matchHeads_complete program query maximumFuel rule headMatch
          ruleMember matched,
        matched⟩

/-- Every finite admitted program has one finite search bound at which head
matching enumerates every and only applicable source rule heads. -/
theorem finiteProgram_has_complete_head_enumeration
    (program : Program) (query : Atom) :
    ∃ maximumFuel,
      (∀ result ∈ matchHeads program query maximumFuel,
        result.rule ∈ program ∧
          result.substitution.applyAtom (encodeScopedAtom .query query) =
            result.substitution.applyAtom
              (encodeScopedAtom .rule result.rule.head)) ∧
      (∀ rule ∈ program, SemanticallyUnifiable query rule →
        ∃ result ∈ matchHeads program query maximumFuel,
          HeadMatches query maximumFuel rule result) := by
  obtain ⟨maximumFuel, bounded⟩ :=
    finiteProgram_has_unification_bound program query
  refine ⟨maximumFuel, ?_, ?_⟩
  · intro result member
    obtain ⟨ruleMember, _, unifies⟩ :=
      matchHeads_every_result_is_source_derived program query maximumFuel
        result member
    exact ⟨ruleMember, unifies⟩
  · intro rule ruleMember unifiable
    exact matchHeads_semantically_exhaustive program query maximumFuel bounded
      rule ruleMember unifiable

/-! ## Executable positive and negative controls -/

def collidingIdentifierRule : Rule :=
  { name := "colliding-identifiers"
    head := collidingIdentifierHead
    body := [] }

def wrongRelationRule : Rule :=
  { name := "wrong-relation"
    head := wrongRelationHead
    body := [] }

def controlProgram : Program :=
  [collidingIdentifierRule, wrongRelationRule]

theorem controlProgram_has_exactly_one_head_match :
    (matchHeads controlProgram collidingIdentifierQuery 100).length = 1 := by
  decide

theorem emptyProgram_has_no_head_matches :
    (matchHeads [] collidingIdentifierQuery 100).length = 0 := by
  decide

end Mettapedia.GSLT.Parsing.HornHeadEnumeration
