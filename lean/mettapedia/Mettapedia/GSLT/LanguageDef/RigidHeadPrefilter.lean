import Mettapedia.GSLT.Parsing.HornCertificate

/-!
# Rigid-constructor prefiltering for first-order rule heads

Before invoking a general unifier, a rule machine can compare the rigid
constructors already visible in a query and a candidate head.  Variables on
either side are wildcards for this preliminary check; constants, integers,
constructor names, list shape, and relation names must agree.

The main theorem proves the useful contrapositive: rejection by this decidable
prefilter rules out every common ground instance.  It is therefore sound to
discard a rejected candidate before freshening, allocating a substitution, or
materializing its body.
-/

namespace Mettapedia.GSLT.LanguageDef.RigidHeadPrefilter

open Mettapedia.GSLT.Parsing.HornCertificate

mutual
  /-- Compare only rigid structure, treating variables on either side as
  compatible with every term. -/
  def compatibleTerm : Term → Term → Bool
    | .var _, _ | _, .var _ => true
    | .atom left, .atom right => left == right
    | .integer left, .integer right => left == right
    | .app left leftArguments, .app right rightArguments =>
        left == right && compatibleTerms leftArguments rightArguments
    | _, _ => false

  /-- Pointwise rigid compatibility, including exact argument-list shape. -/
  def compatibleTerms : Terms → Terms → Bool
    | .nil, .nil => true
    | .cons left lefts, .cons right rights =>
        compatibleTerm left right && compatibleTerms lefts rights
    | _, _ => false
end

/-- Rigid relation, arity, and argument compatibility for rule heads. -/
def compatibleAtom (left right : Atom) : Bool :=
  left.relation == right.relation &&
    compatibleTerms left.arguments right.arguments

mutual
  /-- Two terms with a common ground instance always pass the rigid
  prefilter.  Separate substitutions model variables standardized apart. -/
  theorem compatibleTerm_of_commonGroundInstance
      (left right : Term) (leftSubstitution rightSubstitution : Substitution)
      (target : GroundTerm)
      (leftInstantiated :
        instantiateTerm leftSubstitution left = some target)
      (rightInstantiated :
        instantiateTerm rightSubstitution right = some target) :
      compatibleTerm left right = true := by
    cases left with
    | var identifier => simp [compatibleTerm]
    | atom leftName =>
        cases right with
        | var identifier => simp [compatibleTerm]
        | atom rightName =>
            simp [instantiateTerm] at leftInstantiated rightInstantiated
            subst target
            simp_all [compatibleTerm]
        | integer value =>
            simp [instantiateTerm] at leftInstantiated rightInstantiated
            cases leftInstantiated.trans rightInstantiated.symm
        | app constructor arguments =>
            simp only [instantiateTerm, Option.bind_eq_bind] at rightInstantiated
            cases groundedEq :
                instantiateTerms rightSubstitution arguments with
            | none => simp [groundedEq] at rightInstantiated
            | some grounded =>
                simp [groundedEq] at rightInstantiated
                simp [instantiateTerm] at leftInstantiated
                cases leftInstantiated.trans rightInstantiated.symm
    | integer leftValue =>
        cases right with
        | var identifier => simp [compatibleTerm]
        | atom rightName =>
            simp [instantiateTerm] at leftInstantiated rightInstantiated
            cases leftInstantiated.trans rightInstantiated.symm
        | integer rightValue =>
            simp [instantiateTerm] at leftInstantiated rightInstantiated
            subst target
            simp_all [compatibleTerm]
        | app constructor arguments =>
            simp only [instantiateTerm, Option.bind_eq_bind] at rightInstantiated
            cases groundedEq :
                instantiateTerms rightSubstitution arguments with
            | none => simp [groundedEq] at rightInstantiated
            | some grounded =>
                simp [groundedEq] at rightInstantiated
                simp [instantiateTerm] at leftInstantiated
                cases leftInstantiated.trans rightInstantiated.symm
    | app leftName leftArguments =>
        cases right with
        | var identifier => simp [compatibleTerm]
        | atom rightName =>
            simp only [instantiateTerm, Option.bind_eq_bind] at leftInstantiated
            cases groundedEq :
                instantiateTerms leftSubstitution leftArguments with
            | none => simp [groundedEq] at leftInstantiated
            | some grounded =>
                simp [groundedEq] at leftInstantiated
                simp [instantiateTerm] at rightInstantiated
                cases leftInstantiated.trans rightInstantiated.symm
        | integer rightValue =>
            simp only [instantiateTerm, Option.bind_eq_bind] at leftInstantiated
            cases groundedEq :
                instantiateTerms leftSubstitution leftArguments with
            | none => simp [groundedEq] at leftInstantiated
            | some grounded =>
                simp [groundedEq] at leftInstantiated
                simp [instantiateTerm] at rightInstantiated
                cases leftInstantiated.trans rightInstantiated.symm
        | app rightName rightArguments =>
            simp only [instantiateTerm, Option.bind_eq_bind] at leftInstantiated rightInstantiated
            cases leftGroundEq :
                instantiateTerms leftSubstitution leftArguments with
            | none => simp [leftGroundEq] at leftInstantiated
            | some leftGround =>
                cases rightGroundEq :
                    instantiateTerms rightSubstitution rightArguments with
                | none => simp [rightGroundEq] at rightInstantiated
                | some rightGround =>
                    simp [leftGroundEq] at leftInstantiated
                    simp [rightGroundEq] at rightInstantiated
                    subst target
                    simp_all [compatibleTerm]
                    exact compatibleTerms_of_commonGroundInstance
                      leftArguments rightArguments leftSubstitution
                      rightSubstitution leftGround leftGroundEq rightGroundEq

  /-- Common ground instantiation preserves compatible argument-list shape. -/
  theorem compatibleTerms_of_commonGroundInstance
      (left right : Terms) (leftSubstitution rightSubstitution : Substitution)
      (target : GroundTerms)
      (leftInstantiated :
        instantiateTerms leftSubstitution left = some target)
      (rightInstantiated :
        instantiateTerms rightSubstitution right = some target) :
      compatibleTerms left right = true := by
    cases left with
    | nil =>
        cases right with
        | nil => rfl
        | cons rightHead rightTail =>
            simp only [instantiateTerms, Option.bind_eq_bind] at rightInstantiated
            cases headEq : instantiateTerm rightSubstitution rightHead with
            | none => simp [headEq] at rightInstantiated
            | some groundHead =>
                cases tailEq :
                    instantiateTerms rightSubstitution rightTail with
                | none => simp [headEq, tailEq] at rightInstantiated
                | some groundTail =>
                    simp [headEq, tailEq] at rightInstantiated
                    simp [instantiateTerms] at leftInstantiated
                    cases leftInstantiated.trans rightInstantiated.symm
    | cons leftHead leftTail =>
        cases right with
        | nil =>
            simp only [instantiateTerms, Option.bind_eq_bind] at leftInstantiated
            cases headEq : instantiateTerm leftSubstitution leftHead with
            | none => simp [headEq] at leftInstantiated
            | some groundHead =>
                cases tailEq :
                    instantiateTerms leftSubstitution leftTail with
                | none => simp [headEq, tailEq] at leftInstantiated
                | some groundTail =>
                    simp [headEq, tailEq] at leftInstantiated
                    simp [instantiateTerms] at rightInstantiated
                    cases leftInstantiated.trans rightInstantiated.symm
        | cons rightHead rightTail =>
            simp only [instantiateTerms, Option.bind_eq_bind] at leftInstantiated rightInstantiated
            cases leftHeadEq : instantiateTerm leftSubstitution leftHead with
            | none => simp [leftHeadEq] at leftInstantiated
            | some leftGroundHead =>
                cases leftTailEq :
                    instantiateTerms leftSubstitution leftTail with
                | none => simp [leftHeadEq, leftTailEq] at leftInstantiated
                | some leftGroundTail =>
                    cases rightHeadEq :
                        instantiateTerm rightSubstitution rightHead with
                    | none => simp [rightHeadEq] at rightInstantiated
                    | some rightGroundHead =>
                        cases rightTailEq :
                            instantiateTerms rightSubstitution rightTail with
                        | none =>
                            simp [rightHeadEq, rightTailEq] at rightInstantiated
                        | some rightGroundTail =>
                            simp [leftHeadEq, leftTailEq] at leftInstantiated
                            simp [rightHeadEq, rightTailEq] at rightInstantiated
                            subst target
                            simp_all [compatibleTerms]
                            exact ⟨
                              compatibleTerm_of_commonGroundInstance
                                leftHead rightHead leftSubstitution
                                rightSubstitution leftGroundHead leftHeadEq
                                rightHeadEq,
                              compatibleTerms_of_commonGroundInstance
                                leftTail rightTail leftSubstitution
                                rightSubstitution leftGroundTail leftTailEq
                                rightTailEq⟩
end

/-- Any two atoms with a common ground instance pass the complete head
prefilter. -/
theorem compatibleAtom_of_commonGroundInstance
    (left right : Atom) (leftSubstitution rightSubstitution : Substitution)
    (target : GroundAtom)
    (leftInstantiated :
      instantiateAtom leftSubstitution left = some target)
    (rightInstantiated :
      instantiateAtom rightSubstitution right = some target) :
    compatibleAtom left right = true := by
  unfold instantiateAtom at leftInstantiated rightInstantiated
  cases leftArgumentsEq :
      instantiateTerms leftSubstitution left.arguments with
  | none => simp [leftArgumentsEq] at leftInstantiated
  | some leftArguments =>
      cases rightArgumentsEq :
          instantiateTerms rightSubstitution right.arguments with
      | none => simp [rightArgumentsEq] at rightInstantiated
      | some rightArguments =>
          simp [leftArgumentsEq] at leftInstantiated
          simp [rightArgumentsEq] at rightInstantiated
          subst target
          simp_all [compatibleAtom]
          exact compatibleTerms_of_commonGroundInstance
            left.arguments right.arguments leftSubstitution rightSubstitution
            leftArguments leftArgumentsEq rightArgumentsEq

/-- A negative prefilter result is a certificate that no common ground
instance exists. -/
theorem no_commonGroundInstance_of_incompatibleAtom
    (left right : Atom)
    (incompatible : compatibleAtom left right = false) :
    ¬∃ leftSubstitution rightSubstitution target,
      instantiateAtom leftSubstitution left = some target ∧
      instantiateAtom rightSubstitution right = some target := by
  rintro ⟨leftSubstitution, rightSubstitution, target,
    leftInstantiated, rightInstantiated⟩
  have compatible := compatibleAtom_of_commonGroundInstance
    left right leftSubstitution rightSubstitution target
    leftInstantiated rightInstantiated
  simp [incompatible] at compatible

/-! ## Positive and negative canaries -/

private def variableHead : Atom := {
  relation := "edge"
  arguments := .ofList [.var 0, .app "node" (.ofList [.var 1])] }

private def concreteHead : Atom := {
  relation := "edge"
  arguments := .ofList [.atom "left", .app "node" (.ofList [.integer 3])] }

/-- Variables allow a structurally compatible concrete instance. -/
example : compatibleAtom variableHead concreteHead = true := by
  decide

/-- A nested rigid-constructor disagreement is rejected. -/
example :
    compatibleAtom concreteHead {
      relation := "edge"
      arguments := .ofList [
        .atom "left", .app "leaf" (.ofList [.integer 3])] } = false := by
  decide

/-- Relation disagreement is rejected independently of argument variables. -/
example :
    compatibleAtom variableHead {
      relation := "arc"
      arguments := .ofList [.var 8, .var 9] } = false := by
  decide

/-- Differing argument-list shapes are rejected without invoking unification. -/
example :
    compatibleAtom {
      relation := "opcode"
      arguments := .ofList [.integer 7] } {
      relation := "opcode"
      arguments := .ofList [.integer 7, .integer 9] } = false := by
  decide

end Mettapedia.GSLT.LanguageDef.RigidHeadPrefilter
