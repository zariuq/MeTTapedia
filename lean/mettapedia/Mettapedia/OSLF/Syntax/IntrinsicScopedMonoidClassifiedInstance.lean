import Mettapedia.OSLF.Syntax.IntrinsicScopedAuthoredTermsOnlyControls
import Mettapedia.OSLF.Syntax.MonoidAuthoredComparison
import Mettapedia.OSLF.Syntax.Chapter7MonoidSecondOrderEquations

/-!
# The authored monoid through operational classification

The actual ordered associativity and unit equations supply the program
quotient. The authored empty rewrite inventory supplies genuine firing
trees with no constructors. The resulting categorical model has its
structure-preserving classifying functor and cocontinuous interpretation.
Its represented programs obey precisely the monoid laws; multiplication
order remains observable in an open context.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedMonoidClassifiedInstance

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open FreeBindingTerms (FamilyArgs)
open MonoidEquationRung (sig Srt Op noRewritePresentation monoidE mulQ unitQ)
open IntrinsicScopedLocalPolynomial (LocalRule)
open IntrinsicScopedAuthoredTermsOnlyControls (programAtEquiv)

/-- The authored empty rewrite inventory through the unpruned rule adapter. -/
abbrev rules : List (LocalRule sig) :=
  IntrinsicScopedSharedLocalPolynomialComparison.localRules
    ([] : List (IntrinsicScopedConditionalPolynomial.Rule sig noRewritePresentation.metas))

/-- The original three equations retain their declaration order and full sides. -/
abbrev equations := noRewritePresentation.eqs

abbrev algebra := IntrinsicScopedAuthoredClassifiedInstance.algebra equations
abbrev categoricalModel := IntrinsicScopedAuthoredClassifiedInstance.model rules equations

def classified := IntrinsicScopedAuthoredClassifiedInstance.classified rules equations
def interpretation := IntrinsicScopedAuthoredClassifiedInstance.interpretation rules equations
def restrictionIso := IntrinsicScopedAuthoredClassifiedInstance.restrictionIso rules equations
def recoveredModelIso :=
  IntrinsicScopedAuthoredClassifiedInstance.recoveredModelIso rules equations

/-- Exact intrinsic equation and rewrite coverage, without extra laws. -/
theorem intrinsic_inventory :
    noRewritePresentation.metas = [] ∧
    equations = [MonoidEquationRung.assoc, MonoidEquationRung.leftUnit,
      MonoidEquationRung.rightUnit] ∧ noRewritePresentation.rules = [] ∧ rules = [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The original authoring record has these three ordered names and no rewrites. -/
theorem authored_inventory_coverage :
    MonoidAuthoredComparison.authored.validate = [] ∧
    MonoidAuthoredComparison.authored.equations.map (fun equation => equation.name) =
      ["Assoc", "UnitL", "UnitR"] ∧
    MonoidAuthoredComparison.authored.equations.length = equations.length ∧
    MonoidAuthoredComparison.authored.rewrites.length = rules.length := by
  exact ⟨MonoidAuthoredComparison.authored_valid, rfl, rfl, rfl⟩

/-- Both authored constructors have their original result sort. -/
theorem authored_constructor_coverage :
    MonoidAuthoredComparison.authored.terms.map (fun term => (term.label, term.category)) =
      [("Unit", "M"), ("Mul", "M")] := rfl

/-- The equation-context conversion keeps every original declaration exactly. -/
theorem equation_context_roundtrip :
    (equations.map SecondOrderContext.BaseEquation.ofEmptySchema).map
      SecondOrderContext.BaseEquation.toEmptySchema = equations :=
  SecondOrderContext.MonoidControl.authored_roundtrip

/-- The actual quotient clone's nullary unit operation. -/
def unit {Γ : Ctx sig} : algebra.substitution.Carrier Γ Srt.element :=
  algebra.operation Op.unit .nil

/-- The actual quotient clone's binary multiplication operation. -/
def multiply {Γ : Ctx sig}
    (a b : algebra.substitution.Carrier Γ Srt.element) :
    algebra.substitution.Carrier Γ Srt.element :=
  algebra.operation Op.mul (.cons a (.cons b .nil))

theorem unit_eq_unitQ {Γ : Ctx sig} : (unit (Γ := Γ)) = unitQ := rfl

/-- Quotient-clone multiplication is the original authored quotient multiplication. -/
theorem multiply_eq_mulQ {Γ : Ctx sig}
    (a b : algebra.substitution.Carrier Γ Srt.element) : multiply a b = mulQ a b := by
  induction a using Quotient.inductionOn with
  | _ a =>
    induction b using Quotient.inductionOn with
    | _ b =>
      exact ((BindingEquationQuotientModel.projection equations).raw.map_operation Op.mul
        (FamilyArgs.cons a (FamilyArgs.cons b FamilyArgs.nil))).symm

theorem multiply_assoc {Γ : Ctx sig}
    (a b c : algebra.substitution.Carrier Γ Srt.element) :
    multiply (Γ := Γ) (multiply (Γ := Γ) a b) c =
      multiply (Γ := Γ) a (multiply (Γ := Γ) b c) := by
  have first : (multiply (Γ := Γ) (multiply (Γ := Γ) a b) c : TermQ monoidE Γ Srt.element) =
      mulQ (multiply (Γ := Γ) a b) c := multiply_eq_mulQ _ _
  have second : mulQ (Γ := Γ) (multiply (Γ := Γ) a b) c = mulQ (mulQ a b) c :=
    congrArg (fun x => mulQ (Γ := Γ) x c) (multiply_eq_mulQ a b)
  have third : mulQ (Γ := Γ) a (mulQ b c) = mulQ a (multiply (Γ := Γ) b c) :=
    congrArg (mulQ (Γ := Γ) a) (multiply_eq_mulQ b c).symm
  exact first.trans (second.trans ((MonoidEquationRung.mulQ_assoc a b c).trans
    (third.trans (multiply_eq_mulQ a (multiply (Γ := Γ) b c)).symm)))

theorem multiply_unit_left {Γ : Ctx sig}
    (a : algebra.substitution.Carrier Γ Srt.element) : multiply unit a = a := by
  rw [multiply_eq_mulQ, unit_eq_unitQ]
  exact MonoidEquationRung.unitQ_mulQ a

theorem multiply_unit_right {Γ : Ctx sig}
    (a : algebra.substitution.Carrier Γ Srt.element) : multiply a unit = a := by
  rw [multiply_eq_mulQ, unit_eq_unitQ]
  exact MonoidEquationRung.mulQ_unitQ a

/-- The represented program carrier at the actual quotient clone context. -/
abbrev programs (Γ : Ctx sig) :=
  (categoricalModel.programModel.sort Srt.element).obj
    (Opposite.op (ContextObject.ofList algebra.substitution.toClone Γ))

def program {Γ : Ctx sig} (a : algebra.substitution.Carrier Γ Srt.element) : programs Γ :=
  (programAtEquiv rules equations Γ Srt.element).symm a

/-- Associativity holds inside the classified model's actual program object. -/
theorem program_assoc {Γ : Ctx sig}
    (a b c : algebra.substitution.Carrier Γ Srt.element) :
    program (multiply (multiply a b) c) = program (multiply a (multiply b c)) :=
  congrArg program (multiply_assoc a b c)

theorem program_unit_left {Γ : Ctx sig}
    (a : algebra.substitution.Carrier Γ Srt.element) : program (multiply unit a) = program a :=
  congrArg program (multiply_unit_left a)

theorem program_unit_right {Γ : Ctx sig}
    (a : algebra.substitution.Carrier Γ Srt.element) : program (multiply a unit) = program a :=
  congrArg program (multiply_unit_right a)

/-- The first authored row denotes both sides of the classified program equality. -/
theorem authored_assoc_program {Γ : Ctx sig}
    (σ : Sub sig MonoidEquationRung.assoc.ctx Γ) :
    ∃ env : String → Option (Term sig Γ Srt.element),
      MonoidAuthoredComparison.PatternDenotes env
        (MonoidAuthoredComparison.authored.equations.get ⟨0, by decide⟩).left
        (bind σ (instantiate (fun i : Fin MonoidEquationRung.metas.length => Fin.elim0 i)
          MonoidEquationRung.assoc.lhs)) ∧
      MonoidAuthoredComparison.PatternDenotes env
        (MonoidAuthoredComparison.authored.equations.get ⟨0, by decide⟩).right
        (bind σ (instantiate (fun i : Fin MonoidEquationRung.metas.length => Fin.elim0 i)
          MonoidEquationRung.assoc.rhs)) ∧
      program (Quotient.mk _ (bind σ (instantiate
        (fun i : Fin MonoidEquationRung.metas.length => Fin.elim0 i)
          MonoidEquationRung.assoc.lhs))) =
      program (Quotient.mk _ (bind σ (instantiate
        (fun i : Fin MonoidEquationRung.metas.length => Fin.elim0 i)
          MonoidEquationRung.assoc.rhs))) := by
  obtain ⟨left, right, same⟩ := MonoidAuthoredComparison.authored_assoc_instances σ
  exact ⟨_, left, right, congrArg program (Quotient.sound same)⟩

/-- The second authored row gives the classified left-unit equality. -/
theorem authored_left_unit_program {Γ : Ctx sig}
    (σ : Sub sig MonoidEquationRung.leftUnit.ctx Γ) :
    ∃ env : String → Option (Term sig Γ Srt.element),
      MonoidAuthoredComparison.PatternDenotes env
        (MonoidAuthoredComparison.authored.equations.get ⟨1, by decide⟩).left
        (bind σ (instantiate (fun i : Fin MonoidEquationRung.metas.length => Fin.elim0 i)
          MonoidEquationRung.leftUnit.lhs)) ∧
      MonoidAuthoredComparison.PatternDenotes env
        (MonoidAuthoredComparison.authored.equations.get ⟨1, by decide⟩).right
        (bind σ (instantiate (fun i : Fin MonoidEquationRung.metas.length => Fin.elim0 i)
          MonoidEquationRung.leftUnit.rhs)) ∧
      program (Quotient.mk _ (bind σ (instantiate
        (fun i : Fin MonoidEquationRung.metas.length => Fin.elim0 i)
          MonoidEquationRung.leftUnit.lhs))) =
      program (Quotient.mk _ (bind σ (instantiate
        (fun i : Fin MonoidEquationRung.metas.length => Fin.elim0 i)
          MonoidEquationRung.leftUnit.rhs))) := by
  obtain ⟨left, right, same⟩ := MonoidAuthoredComparison.authored_left_unit_instances σ
  exact ⟨_, left, right, congrArg program (Quotient.sound same)⟩

/-- The third authored row gives the classified right-unit equality. -/
theorem authored_right_unit_program {Γ : Ctx sig}
    (σ : Sub sig MonoidEquationRung.rightUnit.ctx Γ) :
    ∃ env : String → Option (Term sig Γ Srt.element),
      MonoidAuthoredComparison.PatternDenotes env
        (MonoidAuthoredComparison.authored.equations.get ⟨2, by decide⟩).left
        (bind σ (instantiate (fun i : Fin MonoidEquationRung.metas.length => Fin.elim0 i)
          MonoidEquationRung.rightUnit.lhs)) ∧
      MonoidAuthoredComparison.PatternDenotes env
        (MonoidAuthoredComparison.authored.equations.get ⟨2, by decide⟩).right
        (bind σ (instantiate (fun i : Fin MonoidEquationRung.metas.length => Fin.elim0 i)
          MonoidEquationRung.rightUnit.rhs)) ∧
      program (Quotient.mk _ (bind σ (instantiate
        (fun i : Fin MonoidEquationRung.metas.length => Fin.elim0 i)
          MonoidEquationRung.rightUnit.lhs))) =
      program (Quotient.mk _ (bind σ (instantiate
        (fun i : Fin MonoidEquationRung.metas.length => Fin.elim0 i)
          MonoidEquationRung.rightUnit.rhs))) := by
  obtain ⟨left, right, same⟩ := MonoidAuthoredComparison.authored_right_unit_instances σ
  exact ⟨_, left, right, congrArg program (Quotient.sound same)⟩

def firstVariable : algebra.substitution.Carrier [Srt.element, Srt.element] Srt.element :=
  algebra.substitution.injectVar Var.zero

def secondVariable : algebra.substitution.Carrier [Srt.element, Srt.element] Srt.element :=
  algebra.substitution.injectVar (Var.succ Var.zero)

/-- The classified programs distinguish the two multiplication orders. -/
theorem program_variables_not_commutative :
    program (multiply firstVariable secondVariable) ≠
      program (multiply secondVariable firstVariable) := by
  intro same
  have sameTerms := (programAtEquiv rules equations
    [Srt.element, Srt.element] Srt.element).symm.injective same
  rw [multiply_eq_mulQ, multiply_eq_mulQ] at sameTerms
  exact MonoidEquationRung.mulQ_variables_not_commutative sameTerms

/-- Actual classified event sections still require an authored rewrite constructor. -/
theorem no_event (Γ : Ctx sig) (s : Srt)
    (X : IntrinsicScopedConditionalPresheaf.Base algebra)
    (event : (categoricalModel.objects.event Γ s).obj X) : False :=
  IntrinsicScopedAuthoredTermsOnlyControls.no_event algebra Γ s X event

theorem no_closed_reduction {s : Srt} (source target : Term sig [] s) :
    ¬ noRewritePresentation.StepModE source target :=
  MonoidEquationRung.no_reduction source target

/-- No interpreted generic reduction section is introduced at any authored context. -/
theorem no_extended_reduction {Γ : Ctx sig} {s : Srt} (source target : Term sig Γ s) :
    ¬ IntrinsicScopedAuthoredClassifiedReduction.ExtendedReduction
      rules equations source target :=
  IntrinsicScopedAuthoredTermsOnlyControls.no_extended_reduction equations source target

end Mettapedia.OSLF.Binding.IntrinsicScopedMonoidClassifiedInstance
