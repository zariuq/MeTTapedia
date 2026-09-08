import Mathlib.Data.List.Forall2
import Mathlib.Data.Set.Basic

/-!
# Certificates for the admitted first-order Horn fragment

This module gives ordinary GSLT Horn rules a small, generic proof object.  A
certificate supplies a ground substitution for one admitted source rule and a
certificate for every instantiated premise.  The executable checker does not
unify or search: it checks rule membership, substitution well-formedness, the
instantiated head, and every premise recursively.

The main correspondence is bounded and exact: a ground atom is derivable at a
given fuel precisely when some certificate replays at that fuel.
-/

namespace Mettapedia.GSLT.Parsing.HornCertificate

mutual
  inductive Term where
    | var (identifier : Nat)
    | atom (name : String)
    | integer (value : Int)
    | app (constructor : String) (arguments : Terms)
    deriving Repr

  inductive Terms where
    | nil
    | cons (head : Term) (tail : Terms)
    deriving Repr
end

deriving instance DecidableEq for Term, Terms

mutual
  inductive GroundTerm where
    | atom (name : String)
    | integer (value : Int)
    | app (constructor : String) (arguments : GroundTerms)
    deriving Repr

  inductive GroundTerms where
    | nil
    | cons (head : GroundTerm) (tail : GroundTerms)
    deriving Repr
end

deriving instance DecidableEq for GroundTerm, GroundTerms

def Terms.ofList : List Term → Terms
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

def GroundTerms.ofList : List GroundTerm → GroundTerms
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

structure Atom where
  relation : String
  arguments : Terms
  deriving DecidableEq, Repr

structure GroundAtom where
  relation : String
  arguments : GroundTerms
  deriving DecidableEq, Repr

structure Rule where
  name : String
  head : Atom
  body : List Atom
  deriving DecidableEq, Repr

abbrev Program := List Rule
abbrev Substitution := List (Nat × GroundTerm)

def substitutionValid (substitution : Substitution) : Bool :=
  decide substitution.unzip.1.Nodup

private def lookupVariable : Nat → Substitution → Option GroundTerm
  | _, [] => none
  | identifier, (candidate, value) :: rest =>
      if identifier = candidate then some value else lookupVariable identifier rest

mutual
  def instantiateTerm (substitution : Substitution) : Term → Option GroundTerm
    | .var identifier => lookupVariable identifier substitution
    | .atom name => some (.atom name)
    | .integer value => some (.integer value)
    | .app constructor arguments => do
        let grounded ← instantiateTerms substitution arguments
        pure (.app constructor grounded)

  def instantiateTerms (substitution : Substitution) : Terms → Option GroundTerms
    | .nil => some .nil
    | .cons head tail => do
        let groundedHead ← instantiateTerm substitution head
        let groundedTail ← instantiateTerms substitution tail
        pure (.cons groundedHead groundedTail)
end

@[simp] theorem instantiateTerm_var_nil (identifier : Nat) :
    instantiateTerm [] (.var identifier) = none := rfl

@[simp] theorem instantiateTerm_var_cons (identifier candidate : Nat)
    (value : GroundTerm) (rest : Substitution) :
    instantiateTerm ((candidate, value) :: rest) (.var identifier) =
      if identifier = candidate then some value
      else instantiateTerm rest (.var identifier) := rfl

def instantiateAtom
    (substitution : Substitution) (atom : Atom) : Option GroundAtom := do
  let grounded ← instantiateTerms substitution atom.arguments
  pure { relation := atom.relation, arguments := grounded }

def instantiateAtoms
    (substitution : Substitution) (atoms : List Atom) : Option (List GroundAtom) :=
  atoms.mapM (instantiateAtom substitution)

mutual
  inductive DerivesWithin (program : Program) : Nat → GroundAtom → Prop where
    | apply (fuel : Nat) (goal : GroundAtom)
        (rule : Rule) (member : rule ∈ program)
        (substitution : Substitution)
        (valid : substitutionValid substitution = true)
        (goals : List GroundAtom)
        (head : instantiateAtom substitution rule.head = some goal)
        (body : instantiateAtoms substitution rule.body = some goals)
        (premises : DerivationsWithin program fuel goals) :
        DerivesWithin program (fuel + 1) goal

  inductive DerivationsWithin (program : Program) :
      Nat → List GroundAtom → Prop where
    | nil (fuel : Nat) : DerivationsWithin program fuel []
    | cons (head : DerivesWithin program fuel goal)
        (tail : DerivationsWithin program fuel goals) :
        DerivationsWithin program fuel (goal :: goals)
end

mutual
  inductive Certificate where
    | node (rule : Rule) (substitution : Substitution)
        (children : Certificates)
    deriving Repr

  inductive Certificates where
    | nil
    | cons (head : Certificate) (tail : Certificates)
    deriving Repr
end

deriving instance DecidableEq for Certificate, Certificates

def Certificates.toList : Certificates → List Certificate
  | .nil => []
  | .cons head tail => head :: tail.toList

def Certificates.ofList : List Certificate → Certificates
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

def replay (program : Program) : Nat → GroundAtom → Certificate → Bool
  | 0, _, _ => false
  | fuel + 1, goal, .node rule substitution children =>
      decide (rule ∈ program) &&
      substitutionValid substitution &&
      decide (instantiateAtom substitution rule.head = some goal) &&
      match instantiateAtoms substitution rule.body with
      | none => false
      | some goals =>
          decide (goals.length = children.toList.length) &&
          (goals.zip children.toList).all fun pair =>
            replay program fuel pair.1 pair.2

private theorem derivations_of_forall₂
    {program : Program} {fuel : Nat}
    {goals : List GroundAtom} {children : List Certificate}
    (related : List.Forall₂
      (fun goal _ => DerivesWithin program fuel goal) goals children) :
    DerivationsWithin program fuel goals := by
  induction related with
  | nil => exact .nil fuel
  | cons head _ ih => exact .cons head ih

private theorem replayed_children_sound
    {program : Program} {fuel : Nat}
    (inductionHypothesis :
      ∀ (goal : GroundAtom) (certificate : Certificate),
        replay program fuel goal certificate = true →
          DerivesWithin program fuel goal)
    {goals : List GroundAtom} {children : Certificates}
    (lengths : goals.length = children.toList.length)
    (accepted :
      (goals.zip children.toList).all
        (fun pair => replay program fuel pair.1 pair.2) = true) :
    DerivationsWithin program fuel goals := by
  have pointwise :
      ∀ {goal certificate}, (goal, certificate) ∈ goals.zip children.toList →
        DerivesWithin program fuel goal := by
    intro goal certificate member
    apply inductionHypothesis goal certificate
    exact (List.all_eq_true.mp accepted) (goal, certificate) member
  exact derivations_of_forall₂ <|
    List.forall₂_iff_zip.mpr ⟨lengths, pointwise⟩

theorem replay_sound
    (program : Program) (fuel : Nat) (goal : GroundAtom)
    (certificate : Certificate)
    (accepted : replay program fuel goal certificate = true) :
    DerivesWithin program fuel goal := by
  induction fuel generalizing goal certificate with
  | zero => simp [replay] at accepted
  | succ fuel inductionHypothesis =>
      cases certificate with
      | node rule substitution children =>
          cases bodyEquation : instantiateAtoms substitution rule.body with
          | none => simp [replay, bodyEquation] at accepted
          | some goals =>
              simp only [replay, bodyEquation, Bool.and_eq_true,
                decide_eq_true_eq] at accepted
              obtain ⟨⟨⟨member, valid⟩, head⟩, lengths, childrenAccepted⟩ :=
                accepted
              exact .apply fuel goal rule member substitution valid goals head
                bodyEquation
                (replayed_children_sound inductionHypothesis lengths
                  childrenAccepted)

private def replayedChildrenComplete
    {program : Program} {fuel : Nat}
    (inductionHypothesis :
      ∀ (goal : GroundAtom), DerivesWithin program fuel goal →
        ∃ certificate, replay program fuel goal certificate = true)
    {goals : List GroundAtom}
    (derivations : DerivationsWithin program fuel goals) :
    ∃ children : Certificates,
      List.Forall₂
        (fun goal certificate =>
          replay program fuel goal certificate = true)
        goals children.toList :=
  match derivations with
  | .nil _ => ⟨.nil, .nil⟩
  | .cons derivation tail => by
      obtain ⟨certificate, accepted⟩ := inductionHypothesis _ derivation
      obtain ⟨children, childrenAccepted⟩ :=
        replayedChildrenComplete inductionHypothesis tail
      exact ⟨.cons certificate children, .cons accepted childrenAccepted⟩

private theorem all_replay_of_forall₂
    {program : Program} {fuel : Nat}
    {goals : List GroundAtom} {children : Certificates}
    (accepted : List.Forall₂
      (fun goal certificate => replay program fuel goal certificate = true)
      goals children.toList) :
    (goals.zip children.toList).all
      (fun pair => replay program fuel pair.1 pair.2) = true := by
  apply List.all_eq_true.mpr
  intro pair member
  rcases pair with ⟨goal, certificate⟩
  exact List.forall₂_zip accepted member

theorem derivesWithin_complete
    (program : Program) (fuel : Nat) (goal : GroundAtom)
    (derivation : DerivesWithin program fuel goal) :
    ∃ certificate, replay program fuel goal certificate = true := by
  induction fuel generalizing goal with
  | zero => cases derivation
  | succ fuel inductionHypothesis =>
      cases derivation with
      | apply _ _ rule member substitution valid goals head body premises =>
          obtain ⟨children, childrenAccepted⟩ :=
            replayedChildrenComplete inductionHypothesis premises
          refine ⟨.node rule substitution children, ?_⟩
          simp only [replay, body, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨⟨member, valid⟩, head⟩,
            childrenAccepted.length_eq,
            all_replay_of_forall₂ childrenAccepted⟩

theorem replay_iff_derivesWithin
    (program : Program) (fuel : Nat) (goal : GroundAtom) :
    (∃ certificate, replay program fuel goal certificate = true) ↔
      DerivesWithin program fuel goal := by
  constructor
  · rintro ⟨certificate, accepted⟩
    exact replay_sound program fuel goal certificate accepted
  · exact derivesWithin_complete program fuel goal

def derivableResultSet (program : Program) (fuel : Nat)
    (query : GroundTerm → GroundAtom) : Set GroundTerm :=
  { result | DerivesWithin program fuel (query result) }

def certifiedResultSet (program : Program) (fuel : Nat)
    (query : GroundTerm → GroundAtom) : Set GroundTerm :=
  { result | ∃ certificate, replay program fuel (query result) certificate = true }

theorem complete_bounded_result_set_agreement
    (program : Program) (fuel : Nat)
    (query : GroundTerm → GroundAtom) :
    certifiedResultSet program fuel query =
      derivableResultSet program fuel query := by
  ext result
  exact replay_iff_derivesWithin program fuel (query result)

def Ambiguous (results : Set GroundTerm) : Prop :=
  ∃ first ∈ results, ∃ second ∈ results, first ≠ second

theorem complete_bounded_ambiguity_agreement
    (program : Program) (fuel : Nat)
    (query : GroundTerm → GroundAtom) :
    Ambiguous (certifiedResultSet program fuel query) ↔
      Ambiguous (derivableResultSet program fuel query) := by
  rw [complete_bounded_result_set_agreement]

/-! ## Executable positive and negative controls -/

def parentRule : Rule :=
  { name := "parent"
    head :=
      { relation := "parent"
        arguments := Terms.ofList [.var 0, .var 1] }
    body := [] }

def ancestorRule : Rule :=
  { name := "ancestor"
    head :=
      { relation := "ancestor"
        arguments := Terms.ofList [.var 0, .var 1] }
    body :=
      [{ relation := "parent"
         arguments := Terms.ofList [.var 0, .var 1] }] }

def familyProgram : Program := [parentRule, ancestorRule]

def alice : GroundTerm := .atom "alice"
def bob : GroundTerm := .atom "bob"

def parentGoal : GroundAtom :=
  { relation := "parent", arguments := GroundTerms.ofList [alice, bob] }

def ancestorGoal : GroundAtom :=
  { relation := "ancestor", arguments := GroundTerms.ofList [alice, bob] }

def familySubstitution : Substitution := [(0, alice), (1, bob)]

def parentCertificate : Certificate :=
  .node parentRule familySubstitution .nil

def ancestorCertificate : Certificate :=
  .node ancestorRule familySubstitution (.cons parentCertificate .nil)

theorem ancestorCertificate_accepts :
    replay familyProgram 2 ancestorGoal ancestorCertificate = true := by
  decide

theorem ancestorCertificate_is_sound :
    DerivesWithin familyProgram 2 ancestorGoal :=
  replay_sound familyProgram 2 ancestorGoal ancestorCertificate
    ancestorCertificate_accepts

def missingPremiseCertificate : Certificate :=
  .node ancestorRule familySubstitution .nil

theorem missingPremiseCertificate_rejects :
    replay familyProgram 2 ancestorGoal missingPremiseCertificate = false := by
  decide

def duplicateSubstitutionCertificate : Certificate :=
  .node ancestorRule ((0, alice) :: familySubstitution)
    (.cons parentCertificate .nil)

theorem duplicateSubstitutionCertificate_rejects :
    replay familyProgram 2 ancestorGoal duplicateSubstitutionCertificate = false := by
  decide

def mutatedRuleCertificate : Certificate :=
  .node { ancestorRule with name := "not-admitted" }
    familySubstitution (.cons parentCertificate .nil)

theorem mutatedRuleCertificate_rejects :
    replay familyProgram 2 ancestorGoal mutatedRuleCertificate = false := by
  decide

def wrongGroundInstanceCertificate : Certificate :=
  .node ancestorRule [(0, bob), (1, alice)]
    (.cons parentCertificate .nil)

theorem wrongGroundInstanceCertificate_rejects :
    replay familyProgram 2 ancestorGoal wrongGroundInstanceCertificate = false := by
  decide

end Mettapedia.GSLT.Parsing.HornCertificate
