import Mettapedia.OSLF.Syntax.MonoidEquationRung
import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# The authored monoid presentation and its intrinsic equation instance

The Chapter 7 monoid is declared through the canonical `LanguageDef` fields.
The comparison below interprets its variable names and constructor patterns
in the one-sorted intrinsic signature. It records the source's three specific
equations rather than replacing the authored declaration by an isolated model.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.MonoidAuthoredComparison

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding.MonoidEquationRung

private def m : TypeExpr := .base "M"
private def metaVar (name : String) : Pattern := .fvar name
private def unit : Pattern := .apply "Unit" []
private def mul (left right : Pattern) : Pattern :=
  .apply "Mul" [left, right]

private def authoredAssoc : Equation :=
  { name := "Assoc"
    typeContext := [("X", m), ("Y", m), ("Z", m)]
    premises := []
    left := mul (mul (metaVar "X") (metaVar "Y")) (metaVar "Z")
    right := mul (metaVar "X") (mul (metaVar "Y") (metaVar "Z")) }

private def authoredLeftUnit : Equation :=
  { name := "UnitL"
    typeContext := [("X", m)]
    premises := []
    left := mul unit (metaVar "X")
    right := metaVar "X" }

private def authoredRightUnit : Equation :=
  { name := "UnitR"
    typeContext := [("X", m)]
    premises := []
    left := mul (metaVar "X") unit
    right := metaVar "X" }

/-- The canonical authoring record of the book's monoid rung. -/
def authored : LanguageDef :=
  { name := "Monoid"
    types := ["M"]
    terms := [
      { label := "Unit", category := "M", params := [],
        syntaxPattern := [.terminal "e"] },
      { label := "Mul", category := "M",
        params := [.simple "x" m, .simple "y" m],
        syntaxPattern := [.nonTerminal "x", .terminal "*", .nonTerminal "y"] }]
    equations := [authoredAssoc, authoredLeftUnit, authoredRightUnit]
    rewrites := [] }

theorem authored_inventory :
    authored.types.length = 1 ∧ authored.terms.length = 2 ∧
    authored.equations.length = 3 ∧ authored.rewrites.length = 0 := by
  decide

private theorem authored_terms_valid :
    ∀ term ∈ authored.terms, LanguageDef.validateTerm authored term = [] := by
  intro term membership
  simp only [authored, List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl
  · simp +decide [LanguageDef.validateTerm, authored, LanguageDef.typeNames,
      m, TermParam.bodyName, TermParam.binderNames, TermParam.typeExpr]
  · simp +decide [LanguageDef.validateTerm, authored, LanguageDef.typeNames,
      m, TermParam.bodyName, TermParam.binderNames, TermParam.typeExpr]

private theorem authored_equations_valid :
    ∀ equation ∈ authored.equations,
      LanguageDef.validateEquation authored equation = [] := by
  intro equation membership
  simp only [authored, List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl
  all_goals simp +decide [LanguageDef.validateEquation, authored,
    authoredAssoc, authoredLeftUnit, authoredRightUnit,
    LanguageDef.typeNames, LanguageDef.validatePatternConstructors,
    LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
    LanguageDef.patternBinderNames, Pattern.constructorRefs,
    Pattern.constructorRefsList, Pattern.freeFvarNames,
    m, mul, unit, metaVar]

theorem authored_valid : authored.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · decide
  · decide
  · decide
  · decide
  · exact authored_terms_valid
  · exact authored_equations_valid
  · intro rewrite membership
    simp [authored] at membership

/-- Denotation of the supported authored pattern fragment. A term-valued
environment interprets authored free names in an intrinsic context. Other
constructors have no derivation. -/
inductive PatternDenotes {Γ : Ctx sig}
    (env : String → Option (Term sig Γ Srt.element)) :
    Pattern → Term sig Γ Srt.element → Prop where
  | var {name : String} {term : Term sig Γ Srt.element}
      (found : env name = some term) : PatternDenotes env (.fvar name) term
  | unit : PatternDenotes env (.apply "Unit" []) unitT
  | mul {left right : Pattern} {a b : Term sig Γ Srt.element}
      (leftDenotes : PatternDenotes env left a)
      (rightDenotes : PatternDenotes env right b) :
      PatternDenotes env (.apply "Mul" [left, right]) (mulT a b)

/-- Substitution acts pointwise on the environment used to read authored
patterns. -/
def substituteEnvironment {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ)
    (env : String → Option (Term sig Γ Srt.element)) :
    String → Option (Term sig Δ Srt.element) :=
  fun name => (env name).map (bind sigma)

/-- The authored-to-intrinsic interpretation commutes with every sorted
simultaneous substitution, not just closing a ground equation. -/
theorem denotes_substitute {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ)
    {env : String → Option (Term sig Γ Srt.element)}
    {pattern : Pattern} {term : Term sig Γ Srt.element}
    (h : PatternDenotes env pattern term) :
    PatternDenotes (substituteEnvironment sigma env) pattern (bind sigma term) := by
  induction h with
  | var found => exact .var (by simp [substituteEnvironment, found])
  | unit => simpa [bind, bindArgs, unitT] using
      (PatternDenotes.unit (env := substituteEnvironment sigma env))
  | mul leftDenotes rightDenotes ihLeft ihRight =>
      simpa [bind, bindArgs, liftSub, mulT] using
        (PatternDenotes.mul ihLeft ihRight)

private def recognizedHead : Pattern → Bool
  | .fvar _ => true
  | .apply "Unit" [] => true
  | .apply "Mul" [_, _] => true
  | _ => false

theorem denotes_recognizedHead {Γ : Ctx sig}
    {env : String → Option (Term sig Γ Srt.element)}
    {pattern : Pattern} {term : Term sig Γ Srt.element}
    (h : PatternDenotes env pattern term) :
    recognizedHead pattern = true := by
  cases h <;> rfl

private def threeVariables : String →
    Option (Term sig [Srt.element, Srt.element, Srt.element] Srt.element)
  | "X" => some (.var .zero)
  | "Y" => some (.var (.succ .zero))
  | "Z" => some (.var (.succ (.succ .zero)))
  | _ => none

private def oneVariable : String →
    Option (Term sig [Srt.element] Srt.element)
  | "X" => some (.var .zero)
  | _ => none

theorem authored_assoc_lhs :
    PatternDenotes threeVariables authoredAssoc.left
      (instantiate (fun i : Fin metas.length => Fin.elim0 i) assoc.lhs) := by
  change PatternDenotes threeVariables
    (mul (mul (metaVar "X") (metaVar "Y")) (metaVar "Z"))
    (mulT (mulT (.var .zero) (.var (.succ .zero)))
      (.var (.succ (.succ .zero))))
  exact .mul (.mul (.var rfl) (.var rfl)) (.var rfl)

theorem authored_assoc_rhs :
    PatternDenotes threeVariables authoredAssoc.right
      (instantiate (fun i : Fin metas.length => Fin.elim0 i) assoc.rhs) := by
  change PatternDenotes threeVariables
    (mul (metaVar "X") (mul (metaVar "Y") (metaVar "Z")))
    (mulT (.var .zero)
      (mulT (.var (.succ .zero)) (.var (.succ (.succ .zero)))))
  exact .mul (.var rfl) (.mul (.var rfl) (.var rfl))

theorem authored_left_unit_lhs :
    PatternDenotes oneVariable authoredLeftUnit.left
      (instantiate (fun i : Fin metas.length => Fin.elim0 i) leftUnit.lhs) := by
  change PatternDenotes oneVariable (mul unit (metaVar "X"))
    (mulT unitT (.var .zero))
  exact .mul .unit (.var rfl)

theorem authored_left_unit_rhs :
    PatternDenotes oneVariable authoredLeftUnit.right
      (instantiate (fun i : Fin metas.length => Fin.elim0 i) leftUnit.rhs) := by
  change PatternDenotes oneVariable (metaVar "X") (.var .zero)
  exact .var rfl

theorem authored_right_unit_lhs :
    PatternDenotes oneVariable authoredRightUnit.left
      (instantiate (fun i : Fin metas.length => Fin.elim0 i) rightUnit.lhs) := by
  change PatternDenotes oneVariable (mul (metaVar "X") unit)
    (mulT (.var .zero) unitT)
  exact .mul (.var rfl) .unit

theorem authored_right_unit_rhs :
    PatternDenotes oneVariable authoredRightUnit.right
      (instantiate (fun i : Fin metas.length => Fin.elim0 i) rightUnit.rhs) := by
  change PatternDenotes oneVariable (metaVar "X") (.var .zero)
  exact .var rfl

/-- Every closing substitution of the authored associativity row denotes the
corresponding intrinsic axiom instance on both sides. -/
theorem authored_assoc_instances {Γ : Ctx sig}
    (sigma : Sub sig assoc.ctx Γ) :
    PatternDenotes (substituteEnvironment sigma threeVariables)
        authoredAssoc.left
        (bind sigma (instantiate (fun i : Fin metas.length => Fin.elim0 i) assoc.lhs)) ∧
    PatternDenotes (substituteEnvironment sigma threeVariables)
        authoredAssoc.right
        (bind sigma (instantiate (fun i : Fin metas.length => Fin.elim0 i) assoc.rhs)) ∧
    EqClosure monoidE
        (bind sigma (instantiate (fun i : Fin metas.length => Fin.elim0 i) assoc.lhs))
        (bind sigma (instantiate (fun i : Fin metas.length => Fin.elim0 i) assoc.rhs)) := by
  exact ⟨denotes_substitute sigma authored_assoc_lhs,
    denotes_substitute sigma authored_assoc_rhs,
    EqClosure.ax (E := monoidE) (i := ⟨0, by decide⟩)
      (fun i => Fin.elim0 i) sigma⟩

/-- The authored left-unit row is preserved at every intrinsic context. -/
theorem authored_left_unit_instances {Γ : Ctx sig}
    (sigma : Sub sig leftUnit.ctx Γ) :
    PatternDenotes (substituteEnvironment sigma oneVariable)
        authoredLeftUnit.left
        (bind sigma (instantiate (fun i : Fin metas.length => Fin.elim0 i) leftUnit.lhs)) ∧
    PatternDenotes (substituteEnvironment sigma oneVariable)
        authoredLeftUnit.right
        (bind sigma (instantiate (fun i : Fin metas.length => Fin.elim0 i) leftUnit.rhs)) ∧
    EqClosure monoidE
        (bind sigma (instantiate (fun i : Fin metas.length => Fin.elim0 i) leftUnit.lhs))
        (bind sigma (instantiate (fun i : Fin metas.length => Fin.elim0 i) leftUnit.rhs)) := by
  exact ⟨denotes_substitute sigma authored_left_unit_lhs,
    denotes_substitute sigma authored_left_unit_rhs,
    EqClosure.ax (E := monoidE) (i := ⟨1, by decide⟩)
      (fun i => Fin.elim0 i) sigma⟩

/-- The authored right-unit row is preserved at every intrinsic context. -/
theorem authored_right_unit_instances {Γ : Ctx sig}
    (sigma : Sub sig rightUnit.ctx Γ) :
    PatternDenotes (substituteEnvironment sigma oneVariable)
        authoredRightUnit.left
        (bind sigma (instantiate (fun i : Fin metas.length => Fin.elim0 i) rightUnit.lhs)) ∧
    PatternDenotes (substituteEnvironment sigma oneVariable)
        authoredRightUnit.right
        (bind sigma (instantiate (fun i : Fin metas.length => Fin.elim0 i) rightUnit.rhs)) ∧
    EqClosure monoidE
        (bind sigma (instantiate (fun i : Fin metas.length => Fin.elim0 i) rightUnit.lhs))
        (bind sigma (instantiate (fun i : Fin metas.length => Fin.elim0 i) rightUnit.rhs)) := by
  exact ⟨denotes_substitute sigma authored_right_unit_lhs,
    denotes_substitute sigma authored_right_unit_rhs,
    EqClosure.ax (E := monoidE) (i := ⟨2, by decide⟩)
      (fun i => Fin.elim0 i) sigma⟩

/-- The fragment reader rejects an unsupported constructor instead of
quietly assigning it a monoid operation. -/
theorem unknown_constructor_rejected :
    ¬ ∃ term : Term sig [Srt.element] Srt.element,
      PatternDenotes oneVariable
        (.apply "CommutativeMul" [.fvar "X", .fvar "X"]) term := by
  rintro ⟨_, h⟩
  have recognized := denotes_recognizedHead h
  simp [recognizedHead] at recognized

end Mettapedia.OSLF.Binding.MonoidAuthoredComparison
