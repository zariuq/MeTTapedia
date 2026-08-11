import Mettapedia.GSLT.LanguageDef.KernelAuthority

/-!
# Semantic status boundary for TPTP derivations

TPTP inference records attach an SZS success status to an inferred formula.
That status is semantic data: theoremhood, counter-theoremhood, and
equisatisfiability are different relations and cannot share an unindexed
checker contract.

This module records the complete status vocabulary accepted by the TPTP BNF
and leaves its interpretation indexed by the guest logic.  A conservative
classical model interpretation is supplied for the most common statuses.  It
does not assign a meaning to the remaining status codes; language-specific
authorities must do so explicitly.
-/

namespace Mettapedia.Languages.TPTP.StatusSemantics

universe uFormula uModel

/-! ## Complete wire vocabulary -/

/-- Success-status values admitted by the TPTP inference-status grammar. -/
inductive Status where
  | suc | unp | sap | esa | sat | fsa | thm | eqv | tac | wec | eth | tau
  | wtc | wth | cax | sca | tca | wca | cup | csp | ecs | csa | cth | ceq
  | unc | wcc | ect | fun | uns | wuc | wct | scc | uca | noc
deriving DecidableEq, Repr

/-- Canonical three-letter TPTP spelling. -/
def Status.code : Status -> String
  | .suc => "suc" | .unp => "unp" | .sap => "sap" | .esa => "esa"
  | .sat => "sat" | .fsa => "fsa" | .thm => "thm" | .eqv => "eqv"
  | .tac => "tac" | .wec => "wec" | .eth => "eth" | .tau => "tau"
  | .wtc => "wtc" | .wth => "wth" | .cax => "cax" | .sca => "sca"
  | .tca => "tca" | .wca => "wca" | .cup => "cup" | .csp => "csp"
  | .ecs => "ecs" | .csa => "csa" | .cth => "cth" | .ceq => "ceq"
  | .unc => "unc" | .wcc => "wcc" | .ect => "ect" | .fun => "fun"
  | .uns => "uns" | .wuc => "wuc" | .wct => "wct" | .scc => "scc"
  | .uca => "uca" | .noc => "noc"

/-- Fail-closed parsing of an inference-status code. -/
def Status.parse? : String -> Option Status
  | "suc" => some .suc | "unp" => some .unp | "sap" => some .sap
  | "esa" => some .esa | "sat" => some .sat | "fsa" => some .fsa
  | "thm" => some .thm | "eqv" => some .eqv | "tac" => some .tac
  | "wec" => some .wec | "eth" => some .eth | "tau" => some .tau
  | "wtc" => some .wtc | "wth" => some .wth | "cax" => some .cax
  | "sca" => some .sca | "tca" => some .tca | "wca" => some .wca
  | "cup" => some .cup | "csp" => some .csp | "ecs" => some .ecs
  | "csa" => some .csa | "cth" => some .cth | "ceq" => some .ceq
  | "unc" => some .unc | "wcc" => some .wcc | "ect" => some .ect
  | "fun" => some .fun | "uns" => some .uns | "wuc" => some .wuc
  | "wct" => some .wct | "scc" => some .scc | "uca" => some .uca
  | "noc" => some .noc
  | _ => none

@[simp] theorem Status.parse_code (status : Status) :
    Status.parse? status.code = some status := by
  cases status <;> rfl

theorem unknown_status_rejected : Status.parse? "unknown-status" = none := by
  rfl

/-! ## Guest-indexed semantic relations -/

/-- The formula data named by one inference record after parent references
have been resolved. -/
structure RelationClaim (Formula : Type uFormula) where
  parents : List Formula
  inferred : Formula

/-- A guest logic supplies the semantic relation denoted by every status it
chooses to admit.  Unsupported statuses should map to `False`. -/
structure StatusMeaning (Formula : Type uFormula) where
  Meaning : Status -> RelationClaim Formula -> Prop

/-- Minimal classical model interface for the common TSTP status relations.
The common interpretation does not assume decidability of satisfaction. -/
structure ClassicalModelSemantics (Formula : Type uFormula) where
  Model : Type uModel
  satisfies : Model -> Formula -> Prop
  negate : Formula -> Formula
  satisfies_negate : forall model formula,
    satisfies model (negate formula) <-> Not (satisfies model formula)

namespace ClassicalModelSemantics

variable {Formula : Type uFormula} (semantics : ClassicalModelSemantics Formula)

def SatisfiesAll (model : semantics.Model) (formulas : List Formula) : Prop :=
  forall formula, formula ∈ formulas -> semantics.satisfies model formula

def Satisfiable (formulas : List Formula) : Prop :=
  exists model, semantics.SatisfiesAll model formulas

/-- `status(thm)`: every model of all parents satisfies the inferred formula. -/
def TheoremRelation (claim : RelationClaim Formula) : Prop :=
  forall model, semantics.SatisfiesAll model claim.parents ->
    semantics.satisfies model claim.inferred

/-- `status(cth)`: every model of all parents satisfies the negation of the
inferred formula. -/
def CounterTheoremRelation (claim : RelationClaim Formula) : Prop :=
  forall model, semantics.SatisfiesAll model claim.parents ->
    semantics.satisfies model (semantics.negate claim.inferred)

/-- `status(esa)`: the parent collection and inferred singleton have models
together or neither does.  Signature-extension-sensitive guest logics may
replace this common model universe with a stronger indexed interpretation. -/
def EquiSatisfiableRelation (claim : RelationClaim Formula) : Prop :=
  semantics.Satisfiable claim.parents <->
    semantics.Satisfiable [claim.inferred]

/-- A conservative common fragment.  Every other success status fails closed
until a guest language supplies its own admitted semantic interpretation. -/
def commonStatusMeaning : StatusMeaning Formula where
  Meaning
    | .thm => semantics.TheoremRelation
    | .cth => semantics.CounterTheoremRelation
    | .esa => semantics.EquiSatisfiableRelation
    | _ => fun _ => False

end ClassicalModelSemantics

/-! ## Positive and negative semantic canaries -/

namespace Canary

def boolSemantics : ClassicalModelSemantics Bool where
  Model := Unit
  satisfies := fun _ formula => formula = true
  negate := not
  satisfies_negate := by
    intro model formula
    cases formula <;> simp

def theoremClaim : RelationClaim Bool :=
  { parents := [true]
    inferred := true }

def counterTheoremClaim : RelationClaim Bool :=
  { parents := [true]
    inferred := false }

def equiSatisfiableClaim : RelationClaim Bool :=
  { parents := [true]
    inferred := true }

theorem common_three_statuses_hold :
    (boolSemantics.commonStatusMeaning.Meaning .thm theoremClaim) /\
    (boolSemantics.commonStatusMeaning.Meaning .cth counterTheoremClaim) /\
    (boolSemantics.commonStatusMeaning.Meaning .esa equiSatisfiableClaim) := by
  simp [ClassicalModelSemantics.commonStatusMeaning,
    ClassicalModelSemantics.TheoremRelation,
    ClassicalModelSemantics.CounterTheoremRelation,
    ClassicalModelSemantics.EquiSatisfiableRelation,
    ClassicalModelSemantics.Satisfiable,
    ClassicalModelSemantics.SatisfiesAll, theoremClaim,
    counterTheoremClaim, equiSatisfiableClaim, boolSemantics]

/-- An unsupported status is not silently treated as theoremhood. -/
theorem unsupported_status_is_not_common_theorem :
    Not (boolSemantics.commonStatusMeaning.Meaning .suc theoremClaim) := by
  simp [ClassicalModelSemantics.commonStatusMeaning]

/-- Equisatisfiability is genuinely different from theoremhood. -/
theorem false_parent_true_inferred_not_equisatisfiable :
    Not (boolSemantics.commonStatusMeaning.Meaning .esa
      { parents := [false], inferred := true }) := by
  intro equisatisfiable
  have trueSatisfiable : boolSemantics.Satisfiable [true] := by
    exact ⟨(), by simp [ClassicalModelSemantics.SatisfiesAll, boolSemantics]⟩
  have falseSatisfiable := equisatisfiable.mpr trueSatisfiable
  obtain ⟨model, satisfied⟩ := falseSatisfiable
  have impossible : (false : Bool) = true := satisfied false (by simp)
  exact Bool.false_ne_true impossible

end Canary

end Mettapedia.Languages.TPTP.StatusSemantics
