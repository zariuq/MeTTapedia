import Mettapedia.GSLT.LanguageDef.CompiledPlanTermSemantics

/-!
# Rigid-head prefiltering at the compiled-plan boundary

The admitted `CGP1` term carrier already exposes every rigid constructor and
literal in a rule head.  Before allocating a substitution or invoking a
general matcher, a generated machine may compare that structure with the
dynamic query.  Variables on either side remain wildcards.

The decisive theorem is semantic rather than representational: two source
terms that instantiate to the same ground term always pass the prefilter.
Consequently, a negative result is an exact certificate that no common ground
instance exists.  The recognizer mentions no guest vocabulary or proof rule.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanRigidHeadPrefilter

open CompiledPlanAdmission
open CompiledPlanTermSemantics

mutual

/-- Compare only rigid source structure.  Variables deliberately accept every
candidate at this preliminary stage. -/
def compatibleTerm : Term -> Term -> Bool
  | .variable _, _ | _, .variable _ => true
  | .symbol left, .symbol right => left == right
  | .string left, .string right => left == right
  | .integer left, .integer right => left == right
  | .application left leftArguments,
      .application right rightArguments =>
      left == right && compatibleTerms leftArguments rightArguments
  | _, _ => false

/-- Pointwise rigid compatibility includes exact argument-list shape. -/
def compatibleTerms : Terms -> Terms -> Bool
  | .nil, .nil => true
  | .cons left lefts, .cons right rights =>
      compatibleTerm left right && compatibleTerms lefts rights
  | _, _ => false

end

mutual

/-- Two terms with a common ground instance always pass the rigid prefilter.
Separate substitutions model independently scoped query and rule variables. -/
theorem compatibleTerm_of_commonGroundInstance
    (left right : Term) (leftSubstitution rightSubstitution : Substitution)
    (target : GroundTerm)
    (leftInstantiated :
      instantiateTerm leftSubstitution left = some target)
    (rightInstantiated :
      instantiateTerm rightSubstitution right = some target) :
    compatibleTerm left right = true := by
  cases left with
  | «variable» slot => simp [compatibleTerm]
  | symbol leftName =>
      cases right with
      | «variable» slot => simp [compatibleTerm]
      | symbol rightName =>
          simp [instantiateTerm] at leftInstantiated rightInstantiated
          subst target
          simp_all [compatibleTerm]
      | string value =>
          simp [instantiateTerm] at leftInstantiated rightInstantiated
          cases leftInstantiated.trans rightInstantiated.symm
      | integer value =>
          simp [instantiateTerm] at leftInstantiated rightInstantiated
          cases leftInstantiated.trans rightInstantiated.symm
      | application constructor arguments =>
          simp only [instantiateTerm, Option.bind_eq_bind] at rightInstantiated
          cases groundedEq :
              instantiateTerms rightSubstitution arguments with
          | none => simp [groundedEq] at rightInstantiated
          | some grounded =>
              simp [groundedEq] at rightInstantiated
              simp [instantiateTerm] at leftInstantiated
              cases leftInstantiated.trans rightInstantiated.symm
  | string leftValue =>
      cases right with
      | «variable» slot => simp [compatibleTerm]
      | symbol name =>
          simp [instantiateTerm] at leftInstantiated rightInstantiated
          cases leftInstantiated.trans rightInstantiated.symm
      | string rightValue =>
          simp [instantiateTerm] at leftInstantiated rightInstantiated
          subst target
          simp_all [compatibleTerm]
      | integer value =>
          simp [instantiateTerm] at leftInstantiated rightInstantiated
          cases leftInstantiated.trans rightInstantiated.symm
      | application constructor arguments =>
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
      | «variable» slot => simp [compatibleTerm]
      | symbol name =>
          simp [instantiateTerm] at leftInstantiated rightInstantiated
          cases leftInstantiated.trans rightInstantiated.symm
      | string value =>
          simp [instantiateTerm] at leftInstantiated rightInstantiated
          cases leftInstantiated.trans rightInstantiated.symm
      | integer rightValue =>
          simp [instantiateTerm] at leftInstantiated rightInstantiated
          subst target
          simp_all [compatibleTerm]
      | application constructor arguments =>
          simp only [instantiateTerm, Option.bind_eq_bind] at rightInstantiated
          cases groundedEq :
              instantiateTerms rightSubstitution arguments with
          | none => simp [groundedEq] at rightInstantiated
          | some grounded =>
              simp [groundedEq] at rightInstantiated
              simp [instantiateTerm] at leftInstantiated
              cases leftInstantiated.trans rightInstantiated.symm
  | application leftName leftArguments =>
      cases right with
      | «variable» slot => simp [compatibleTerm]
      | symbol name =>
          simp only [instantiateTerm, Option.bind_eq_bind] at leftInstantiated
          cases groundedEq :
              instantiateTerms leftSubstitution leftArguments with
          | none => simp [groundedEq] at leftInstantiated
          | some grounded =>
              simp [groundedEq] at leftInstantiated
              simp [instantiateTerm] at rightInstantiated
              cases leftInstantiated.trans rightInstantiated.symm
      | string value =>
          simp only [instantiateTerm, Option.bind_eq_bind] at leftInstantiated
          cases groundedEq :
              instantiateTerms leftSubstitution leftArguments with
          | none => simp [groundedEq] at leftInstantiated
          | some grounded =>
              simp [groundedEq] at leftInstantiated
              simp [instantiateTerm] at rightInstantiated
              cases leftInstantiated.trans rightInstantiated.symm
      | integer value =>
          simp only [instantiateTerm, Option.bind_eq_bind] at leftInstantiated
          cases groundedEq :
              instantiateTerms leftSubstitution leftArguments with
          | none => simp [groundedEq] at leftInstantiated
          | some grounded =>
              simp [groundedEq] at leftInstantiated
              simp [instantiateTerm] at rightInstantiated
              cases leftInstantiated.trans rightInstantiated.symm
      | application rightName rightArguments =>
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
              cases tailEq : instantiateTerms rightSubstitution rightTail with
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
              cases tailEq : instantiateTerms leftSubstitution leftTail with
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

/-- A negative prefilter result certifies that no pair of substitutions can
produce a shared ground instance. -/
theorem no_commonGroundInstance_of_incompatibleTerm
    (left right : Term) (incompatible : compatibleTerm left right = false) :
    ¬∃ leftSubstitution rightSubstitution target,
      instantiateTerm leftSubstitution left = some target ∧
      instantiateTerm rightSubstitution right = some target := by
  rintro ⟨leftSubstitution, rightSubstitution, target,
    leftInstantiated, rightInstantiated⟩
  have compatible := compatibleTerm_of_commonGroundInstance
    left right leftSubstitution rightSubstitution target
    leftInstantiated rightInstantiated
  simp [incompatible] at compatible

/-- Source-order candidate filtering performed before any matcher allocation. -/
def filterCompatible (query : Term) (candidates : List Term) : List Term :=
  candidates.filter fun candidate => compatibleTerm candidate query

/-- Every candidate with a common ground instance survives source-order
prefiltering. -/
theorem mem_filterCompatible_of_commonGroundInstance
    (query candidate : Term) (candidates : List Term)
    (member : candidate ∈ candidates)
    (leftSubstitution rightSubstitution : Substitution) (target : GroundTerm)
    (candidateInstantiated :
      instantiateTerm leftSubstitution candidate = some target)
    (queryInstantiated :
      instantiateTerm rightSubstitution query = some target) :
    candidate ∈ filterCompatible query candidates := by
  simp only [filterCompatible, List.mem_filter, member, true_and]
  exact compatibleTerm_of_commonGroundInstance candidate query
    leftSubstitution rightSubstitution target candidateInstantiated
    queryInstantiated

def sourceMatcherAttempts (candidates : List Term) : Nat := candidates.length

def filteredMatcherAttempts (query : Term) (candidates : List Term) : Nat :=
  (filterCompatible query candidates).length

/-- Prefiltering never schedules more general matcher attempts. -/
theorem filteredMatcherAttempts_le
    (query : Term) (candidates : List Term) :
    filteredMatcherAttempts query candidates <=
      sourceMatcherAttempts candidates := by
  exact List.length_filter_le
    (fun candidate => compatibleTerm candidate query) candidates

/-! ## Independent witnesses and rejecting controls -/

private def parserCandidate : Term :=
  .application [1]
    (.cons (.symbol [2])
      (.cons (.application [3] (.cons (.variable 0) .nil)) .nil))

private def parserQuery : Term :=
  .application [1]
    (.cons (.symbol [2])
      (.cons (.application [4] (.cons (.integer 5) .nil)) .nil))

/-- A nested parser constructor disagreement is rejected. -/
example : compatibleTerm parserCandidate parserQuery = false := by
  decide

private def proofCandidate : Term :=
  .application [10]
    (.cons (.application [11] (.cons (.variable 0) .nil))
      (.cons (.string [12]) .nil))

private def proofQuery : Term :=
  .application [10]
    (.cons (.application [11] (.cons (.symbol [13]) .nil))
      (.cons (.string [12]) .nil))

/-- A proof-shaped query compatible through a variable passes. -/
example : compatibleTerm proofCandidate proofQuery = true := by
  decide

/-- Literal sort disagreement fails before matching. -/
example : compatibleTerm (.string [1]) (.symbol [1]) = false := by
  decide

/-- Argument-list shape disagreement fails before matching. -/
example :
    compatibleTerm
      (.application [20] (.cons (.integer 1) .nil))
      (.application [20]
        (.cons (.integer 1) (.cons (.integer 2) .nil))) = false := by
  decide

end Mettapedia.GSLT.LanguageDef.CompiledPlanRigidHeadPrefilter
