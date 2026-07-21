import Mettapedia.GSLT.Parsing.HornCertificate
import Mettapedia.Logic.LP.Unification
import Mettapedia.Logic.LP.UnificationComplete
import Mettapedia.Logic.LP.TotalUnification

/-!
# Occurs-checked unification for serialized Horn syntax

The executable syntax-GSLT compiler discovers candidate specializations by
unifying a ground grammar query with admitted Horn rule heads.  This module
connects the serialized Horn term representation to the existing proved
Martelli--Montanari unifier.  Function and relation arities are carried in
their encoded symbols, so malformed cross-arity applications cannot unify.

The current result proves soundness and semantic completeness of unification
on encoded Horn atoms.  Recovering canonical `SpecializationCertificate`
values from the resulting substitution is the next compiler-enumeration seam.
-/

namespace Mettapedia.GSLT.Parsing.HornUnification

open HornCertificate

inductive Constant where
  | atom (name : String)
  | integer (value : Int)
  deriving DecidableEq, Repr

structure FunctionSymbol where
  name : String
  arity : Nat
  deriving DecidableEq, Repr

structure RelationSymbol where
  name : String
  arity : Nat
  deriving DecidableEq, Repr

abbrev signature : Mettapedia.Logic.LP.LPSignature where
  constants := Constant
  vars := Nat
  relationSymbols := RelationSymbol
  relationArity := RelationSymbol.arity
  functionSymbols := FunctionSymbol
  functionArity := FunctionSymbol.arity

mutual
  def encodeTerm : HornCertificate.Term → Mettapedia.Logic.LP.Term signature
    | .var identifier => .var identifier
    | .atom name => .const (.atom name)
    | .integer value => .const (.integer value)
    | .app constructor arguments =>
        let encoded := encodeTerms arguments
        .app { name := constructor, arity := encoded.length }
          fun index => encoded.get index

  def encodeTerms : HornCertificate.Terms →
      List (Mettapedia.Logic.LP.Term signature)
    | .nil => []
    | .cons head tail => encodeTerm head :: encodeTerms tail
end

def encodeAtom (atom : HornCertificate.Atom) :
    Mettapedia.Logic.LP.Atom signature :=
  let arguments := encodeTerms atom.arguments
  { symbol := { name := atom.relation, arity := arguments.length }
    args := fun index => arguments.get index }

def unify (left right : HornCertificate.Atom) (fuel : Nat := 1000) :
    Option (Mettapedia.Logic.LP.Subst signature) :=
  Mettapedia.Logic.LP.unifyAtoms (encodeAtom left) (encodeAtom right) fuel

theorem unify_sound (left right : HornCertificate.Atom) (fuel : Nat)
    (substitution : Mettapedia.Logic.LP.Subst signature)
    (accepted : unify left right fuel = some substitution) :
    substitution.applyAtom (encodeAtom left) =
      substitution.applyAtom (encodeAtom right) :=
  Mettapedia.Logic.LP.unifyAtoms_sound (encodeAtom left) (encodeAtom right)
    fuel substitution (by simpa [unify] using accepted)

private theorem unifyAtoms_complete {σ : Mettapedia.Logic.LP.LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (left right : Mettapedia.Logic.LP.Atom σ)
    (unifiable : ∃ substitution : Mettapedia.Logic.LP.Subst σ,
      substitution.applyAtom left = substitution.applyAtom right) :
    ∃ fuel substitution,
      Mettapedia.Logic.LP.unifyAtoms left right fuel = some substitution := by
  obtain ⟨leftSymbol, leftArguments⟩ := left
  obtain ⟨rightSymbol, rightArguments⟩ := right
  obtain ⟨candidate, candidateUnifies⟩ := unifiable
  have symbolEq : leftSymbol = rightSymbol := by
    have symbols := congrArg Mettapedia.Logic.LP.Atom.symbol candidateUnifies
    simpa [Mettapedia.Logic.LP.Subst.applyAtom] using symbols
  subst rightSymbol
  have argumentsUnify : ∀ index,
      candidate.applyTerm (leftArguments index) =
        candidate.applyTerm (rightArguments index) := by
    have atoms := candidateUnifies
    simp only [Mettapedia.Logic.LP.Subst.applyAtom,
      Mettapedia.Logic.LP.Atom.mk.injEq, heq_eq_eq, true_and] at atoms
    exact fun index => congrFun atoms index
  have equationsUnify :
      Mettapedia.Logic.LP.Unifies candidate
        (Mettapedia.Logic.LP.finPairsToList leftArguments rightArguments) := by
    intro equation member
    simp only [Mettapedia.Logic.LP.finPairsToList, List.mem_map,
      List.mem_finRange,
      true_and] at member
    obtain ⟨index, rfl⟩ := member
    exact argumentsUnify index
  obtain ⟨fuel, substitution, accepted⟩ :=
    Mettapedia.Logic.LP.unifyFuel_exists_of_unifies
      (eqs := Mettapedia.Logic.LP.finPairsToList leftArguments rightArguments)
      ⟨candidate, equationsUnify⟩
  exact ⟨fuel, substitution, by
    simpa [Mettapedia.Logic.LP.unifyAtoms] using accepted⟩

theorem unify_complete (left right : HornCertificate.Atom)
    (unifiable : ∃ substitution : Mettapedia.Logic.LP.Subst signature,
      substitution.applyAtom (encodeAtom left) =
        substitution.applyAtom (encodeAtom right)) :
    ∃ fuel substitution, unify left right fuel = some substitution := by
  simpa [unify] using
    (unifyAtoms_complete (encodeAtom left) (encodeAtom right) unifiable)

/-! ## Apart-renamed unification for compiler rule matching

The compiler's query variables and a source rule's variables are independent
even when their serialized numeric identifiers coincide.  Keeping their
origins in the unification signature makes that invariant structural rather
than dependent on an informal fresh-number convention.
-/

inductive VariableOrigin where
  | query
  | rule
  deriving DecidableEq, Repr

structure ScopedVariable where
  origin : VariableOrigin
  identifier : Nat
  deriving DecidableEq, Repr

abbrev compilerSignature : Mettapedia.Logic.LP.LPSignature where
  constants := Constant
  vars := ScopedVariable
  relationSymbols := RelationSymbol
  relationArity := RelationSymbol.arity
  functionSymbols := FunctionSymbol
  functionArity := FunctionSymbol.arity

mutual
  def encodeScopedTerm (origin : VariableOrigin) :
      HornCertificate.Term → Mettapedia.Logic.LP.Term compilerSignature
    | .var identifier => .var { origin, identifier }
    | .atom name => .const (.atom name)
    | .integer value => .const (.integer value)
    | .app constructor arguments =>
        let encoded := encodeScopedTerms origin arguments
        .app { name := constructor, arity := encoded.length }
          fun index => encoded.get index

  def encodeScopedTerms (origin : VariableOrigin) : HornCertificate.Terms →
      List (Mettapedia.Logic.LP.Term compilerSignature)
    | .nil => []
    | .cons head tail =>
        encodeScopedTerm origin head :: encodeScopedTerms origin tail
end

def encodeScopedAtom (origin : VariableOrigin) (atom : HornCertificate.Atom) :
    Mettapedia.Logic.LP.Atom compilerSignature :=
  let arguments := encodeScopedTerms origin atom.arguments
  { symbol := { name := atom.relation, arity := arguments.length }
    args := fun index => arguments.get index }

def unifyApart (query ruleHead : HornCertificate.Atom) (fuel : Nat := 1000) :
    Option (Mettapedia.Logic.LP.Subst compilerSignature) :=
  Mettapedia.Logic.LP.unifyAtoms
    (encodeScopedAtom .query query) (encodeScopedAtom .rule ruleHead) fuel

theorem unifyApart_sound (query ruleHead : HornCertificate.Atom) (fuel : Nat)
    (substitution : Mettapedia.Logic.LP.Subst compilerSignature)
    (accepted : unifyApart query ruleHead fuel = some substitution) :
    substitution.applyAtom (encodeScopedAtom .query query) =
      substitution.applyAtom (encodeScopedAtom .rule ruleHead) :=
  Mettapedia.Logic.LP.unifyAtoms_sound
    (encodeScopedAtom .query query) (encodeScopedAtom .rule ruleHead)
    fuel substitution (by simpa [unifyApart] using accepted)

theorem unifyApart_complete (query ruleHead : HornCertificate.Atom)
    (unifiable : ∃ substitution : Mettapedia.Logic.LP.Subst compilerSignature,
      substitution.applyAtom (encodeScopedAtom .query query) =
        substitution.applyAtom (encodeScopedAtom .rule ruleHead)) :
    ∃ fuel substitution, unifyApart query ruleHead fuel = some substitution := by
  simpa [unifyApart] using
    (unifyAtoms_complete (encodeScopedAtom .query query)
      (encodeScopedAtom .rule ruleHead) unifiable)

/-- Fuel-free compiler unification.  Unlike `unifyApart`, `none` here is a
proved logical failure rather than an exhausted internal search budget. -/
def unifyApartTotal (query ruleHead : HornCertificate.Atom) :
    Option (Mettapedia.Logic.LP.Subst compilerSignature) :=
  Mettapedia.Logic.LP.unifyAtomsTotal
    (encodeScopedAtom .query query) (encodeScopedAtom .rule ruleHead)

theorem unifyApartTotal_sound (query ruleHead : HornCertificate.Atom)
    (substitution : Mettapedia.Logic.LP.Subst compilerSignature)
    (accepted : unifyApartTotal query ruleHead = some substitution) :
    substitution.applyAtom (encodeScopedAtom .query query) =
      substitution.applyAtom (encodeScopedAtom .rule ruleHead) :=
  Mettapedia.Logic.LP.unifyAtomsTotal_sound
    (encodeScopedAtom .query query) (encodeScopedAtom .rule ruleHead)
    substitution accepted

theorem unifyApartTotal_complete (query ruleHead : HornCertificate.Atom)
    (unifiable : ∃ substitution : Mettapedia.Logic.LP.Subst compilerSignature,
      substitution.applyAtom (encodeScopedAtom .query query) =
        substitution.applyAtom (encodeScopedAtom .rule ruleHead)) :
    ∃ substitution, unifyApartTotal query ruleHead = some substitution :=
  Mettapedia.Logic.LP.unifyAtomsTotal_complete
    (encodeScopedAtom .query query) (encodeScopedAtom .rule ruleHead) unifiable

theorem unifyApartTotal_mgu (query ruleHead : HornCertificate.Atom)
    (substitution : Mettapedia.Logic.LP.Subst compilerSignature)
    (accepted : unifyApartTotal query ruleHead = some substitution)
    (candidate : Mettapedia.Logic.LP.Subst compilerSignature)
    (unifies : candidate.applyAtom (encodeScopedAtom .query query) =
      candidate.applyAtom (encodeScopedAtom .rule ruleHead)) :
    substitution.moreGeneral candidate :=
  Mettapedia.Logic.LP.unifyAtomsTotal_mgu
    (encodeScopedAtom .query query) (encodeScopedAtom .rule ruleHead)
    substitution accepted candidate unifies

theorem unifyApartTotal_none_iff_not_unifiable
    (query ruleHead : HornCertificate.Atom) :
    unifyApartTotal query ruleHead = none ↔
      ¬∃ substitution : Mettapedia.Logic.LP.Subst compilerSignature,
        substitution.applyAtom (encodeScopedAtom .query query) =
          substitution.applyAtom (encodeScopedAtom .rule ruleHead) :=
  Mettapedia.Logic.LP.unifyAtomsTotal_none_iff_not_unifiable
    (encodeScopedAtom .query query) (encodeScopedAtom .rule ruleHead)

/-- Search every unification fuel up to and including `maximumFuel`.  This
avoids treating an arbitrary single fuel choice as part of the language. -/
def firstUnifier (query ruleHead : HornCertificate.Atom) : Nat →
    Option (Nat × Mettapedia.Logic.LP.Subst compilerSignature)
  | 0 => (unifyApart query ruleHead 0).map fun substitution => (0, substitution)
  | maximumFuel + 1 =>
      match firstUnifier query ruleHead maximumFuel with
      | some result => some result
      | none =>
          (unifyApart query ruleHead (maximumFuel + 1)).map fun substitution =>
            (maximumFuel + 1, substitution)

theorem firstUnifier_sound (query ruleHead : HornCertificate.Atom)
    (maximumFuel foundFuel : Nat)
    (substitution : Mettapedia.Logic.LP.Subst compilerSignature)
    (accepted : firstUnifier query ruleHead maximumFuel =
      some (foundFuel, substitution)) :
    foundFuel ≤ maximumFuel ∧
      unifyApart query ruleHead foundFuel = some substitution := by
  induction maximumFuel generalizing foundFuel substitution with
  | zero =>
      cases result : unifyApart query ruleHead 0 with
      | none => simp [firstUnifier, result] at accepted
      | some resultSubstitution =>
          simp [firstUnifier, result] at accepted
          obtain ⟨rfl, rfl⟩ := accepted
          exact ⟨Nat.le_refl 0, result⟩
  | succ maximumFuel inductionHypothesis =>
      cases earlier : firstUnifier query ruleHead maximumFuel with
      | some result =>
          simp [firstUnifier, earlier] at accepted
          obtain ⟨earlierFuel, earlierSubstitution⟩ := result
          injection accepted with fuelEq substitutionEq
          subst foundFuel
          subst substitution
          obtain ⟨bound, succeeds⟩ :=
            inductionHypothesis earlierFuel earlierSubstitution earlier
          exact ⟨Nat.le.step bound, succeeds⟩
      | none =>
          cases latest : unifyApart query ruleHead (maximumFuel + 1) with
          | none => simp [firstUnifier, earlier, latest] at accepted
          | some latestSubstitution =>
              simp [firstUnifier, earlier, latest] at accepted
              obtain ⟨rfl, rfl⟩ := accepted
              exact ⟨Nat.le_refl _, latest⟩

theorem firstUnifier_complete (query ruleHead : HornCertificate.Atom)
    (maximumFuel fuel : Nat)
    (substitution : Mettapedia.Logic.LP.Subst compilerSignature)
    (within : fuel ≤ maximumFuel)
    (accepted : unifyApart query ruleHead fuel = some substitution) :
    (firstUnifier query ruleHead maximumFuel).isSome = true := by
  induction maximumFuel generalizing fuel substitution with
  | zero =>
      have : fuel = 0 := Nat.eq_zero_of_le_zero within
      subst fuel
      simp [firstUnifier, accepted]
  | succ maximumFuel inductionHypothesis =>
      cases Nat.eq_or_lt_of_le within with
      | inl equal =>
          subst fuel
          cases earlier : firstUnifier query ruleHead maximumFuel with
          | some result => simp [firstUnifier, earlier]
          | none => simp [firstUnifier, earlier, accepted]
      | inr less =>
          have earlierAccepted := inductionHypothesis fuel substitution
            (Nat.le_of_lt_succ less) accepted
          cases earlier : firstUnifier query ruleHead maximumFuel with
          | none => simp [earlier] at earlierAccepted
          | some result => simp [firstUnifier, earlier]

theorem firstUnifier_semantically_complete (query ruleHead : HornCertificate.Atom)
    (unifiable : ∃ substitution : Mettapedia.Logic.LP.Subst compilerSignature,
      substitution.applyAtom (encodeScopedAtom .query query) =
        substitution.applyAtom (encodeScopedAtom .rule ruleHead)) :
    ∃ maximumFuel, (firstUnifier query ruleHead maximumFuel).isSome = true := by
  obtain ⟨fuel, substitution, accepted⟩ :=
    unifyApart_complete query ruleHead unifiable
  exact ⟨fuel, firstUnifier_complete query ruleHead fuel fuel substitution
    (Nat.le_refl fuel) accepted⟩

/-! ## Executable positive and negative controls -/

def queryAtom : HornCertificate.Atom :=
  { relation := "parse"
    arguments := Terms.ofList [
      .app "char" (Terms.ofList [.app "cp" (Terms.ofList [.integer 97])]),
      .var 0,
      .var 1,
      .var 2] }

def matchingHead : HornCertificate.Atom :=
  { relation := "parse"
    arguments := Terms.ofList [
      .app "char" (Terms.ofList [.var 10]),
      .app "cons" (Terms.ofList [.var 10, .var 11]),
      .var 10,
      .var 11] }

def wrongRelationHead : HornCertificate.Atom :=
  { matchingHead with relation := "not-parse" }

def occursCheckHead : HornCertificate.Atom :=
  { relation := "parse"
    arguments := Terms.ofList [
      .var 0,
      .app "wrap" (Terms.ofList [.var 0]),
      .atom "value",
      .atom "nil"] }

def occursCheckQuery : HornCertificate.Atom :=
  { relation := "parse"
    arguments := Terms.ofList [
      .var 1,
      .var 1,
      .atom "value",
      .atom "nil"] }

def collidingIdentifierQuery : HornCertificate.Atom :=
  { relation := "parse", arguments := Terms.ofList [.var 0] }

def collidingIdentifierHead : HornCertificate.Atom :=
  { relation := "parse"
    arguments := Terms.ofList [.app "wrap" (Terms.ofList [.var 0])] }

theorem matchingHead_accepts :
    (unify queryAtom matchingHead 100).isSome = true := by
  decide

theorem wrongRelation_rejects :
    unify queryAtom wrongRelationHead 100 = none := by
  decide

theorem occursCheck_rejects :
    unify occursCheckQuery occursCheckHead 100 = none := by
  decide

/-- Query variable `0` and source-rule variable `0` are distinct variables.
The unscoped wrapper rejects this pair as an occurs-check cycle; the compiler
matcher correctly apart-renames the two namespaces and accepts it. -/
theorem unscoped_collidingIdentifier_rejects :
    unify collidingIdentifierQuery collidingIdentifierHead 100 = none := by
  decide

theorem apart_collidingIdentifier_accepts :
    (unifyApart collidingIdentifierQuery collidingIdentifierHead 100).isSome =
      true := by
  decide

/-- The bounded API cannot distinguish this valid match from exhaustion at
fuel zero; the total API accepts it without a resource parameter. -/
theorem zeroFuel_is_incomplete_but_total_accepts :
    unifyApart collidingIdentifierQuery collidingIdentifierHead 0 = none ∧
      (unifyApartTotal collidingIdentifierQuery collidingIdentifierHead).isSome =
        true := by
  constructor
  · decide
  · cases bounded : unifyApart collidingIdentifierQuery collidingIdentifierHead 100 with
    | none =>
        have := apart_collidingIdentifier_accepts
        simp [bounded] at this
    | some substitution =>
        have unifies := unifyApart_sound collidingIdentifierQuery
          collidingIdentifierHead 100 substitution bounded
        obtain ⟨totalSubstitution, accepted⟩ :=
          unifyApartTotal_complete collidingIdentifierQuery
            collidingIdentifierHead ⟨substitution, unifies⟩
        simp [accepted]

theorem total_wrongRelation_rejects :
    unifyApartTotal queryAtom wrongRelationHead = none := by
  decide

theorem total_occursCheck_rejects :
    unifyApartTotal occursCheckQuery occursCheckHead = none := by
  rw [unifyApartTotal_none_iff_not_unifiable]
  intro unifiable
  obtain ⟨fuel, substitution, accepted⟩ :=
    unifyApart_complete occursCheckQuery occursCheckHead unifiable
  have rejected : unifyApart occursCheckQuery occursCheckHead fuel = none := by
    cases fuel with
    | zero => rfl
    | succ fuel =>
        cases fuel with
        | zero =>
            simp [unifyApart, encodeScopedAtom, encodeScopedTerms,
              encodeScopedTerm, HornCertificate.Terms.ofList,
              occursCheckQuery, occursCheckHead,
              Mettapedia.Logic.LP.unifyAtoms,
              Mettapedia.Logic.LP.finPairsToList, List.finRange,
              Mettapedia.Logic.LP.unifyFuel]
        | succ fuel =>
            simp [unifyApart, encodeScopedAtom, encodeScopedTerms,
              encodeScopedTerm, HornCertificate.Terms.ofList,
              occursCheckQuery, occursCheckHead,
              Mettapedia.Logic.LP.unifyAtoms,
              Mettapedia.Logic.LP.finPairsToList, List.finRange,
              Mettapedia.Logic.LP.unifyFuel,
              Mettapedia.Logic.LP.Subst.applyEqs,
              Mettapedia.Logic.LP.Subst.applyTerm,
              Mettapedia.Logic.LP.Subst.single,
              Mettapedia.Logic.LP.Term.occursIn]
  rw [rejected] at accepted
  contradiction

end Mettapedia.GSLT.Parsing.HornUnification
