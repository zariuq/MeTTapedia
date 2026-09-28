import Mettapedia.OSLF.Syntax.RhoFreeBindingEquationModel

/-!
# The Drop boundary of the local communication-only rho profile

Finding Mind Chapter 7 writes a separate Drop reduction alongside Comm.
The intrinsic rho presentation used here currently has Comm as its only
rewrite. This file compares the two at a closed null-process instance. It
does not identify the local binary-parallel/ACU presentation with the book's
bag-valued, conditional source presentation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoDropBoundary

open Mettapedia.OSLF.Binding.RhoSchema

private theorem emptyArgs_unique {sorts : List Srt}
    (args : Args sig [] sorts) : args = .nil := by
  cases args
  rfl

/-- A closed reflective round trip and its expected Drop target. -/
def dropQuotedNil : Term sig [] Srt.pr :=
  .op Op.drp (.cons (.op Op.quo (.cons nilP .nil)) .nil)

/-- A communication redex has a parallel head, whereas the reflective
round trip has a drop head. -/
theorem no_comm_at_drop_root (target : Term sig [] Srt.pr) :
    ¬ RootStep comm dropQuotedNil target := by
  intro h
  obtain ⟨_, shape⟩ := rootStep_lhs_shape comm h
  change dropQuotedNil = Term.op Op.par _ at shape
  cases shape

/-- Even contextual closure of the local Comm rule cannot reduce this
particular closed round trip: any proposed hole beneath drop and quote would
force a communication step from the null process. -/
theorem no_comm_at_drop (target : Term sig [] Srt.pr) :
    ¬ Step comm dropQuotedNil target := by
  rintro ⟨K, a, b, linear, fires, source, -⟩
  cases K with
  | var v =>
      cases v with
      | zero =>
          exact no_comm_at_drop_root b (source ▸ fires)
      | succ old => cases old
  | op op args =>
      cases op with
      | nil =>
          cases args
          exact absurd linear (by decide)
      | par => cases source
      | out => cases source
      | inp => cases source
      | drp =>
          cases args with
          | cons name rest =>
              have rest_eq : rest = Args.nil := emptyArgs_unique rest
              subst rest
              cases name with
              | var v =>
                  cases v with
                  | succ old => cases old
              | op nameOp nameArgs =>
                  cases nameOp with
                  | quo =>
                      cases nameArgs with
                      | cons inner more =>
                          have more_eq : more = Args.nil := emptyArgs_unique more
                          subst more
                          have innerSource : inst inner a = nilP := by
                            change Term.op (S := sig) (Γ := []) Op.drp
                                (.cons (Term.op (S := sig) (Γ := []) Op.quo
                                  (.cons (inst inner a) .nil)) .nil) =
                              Term.op (S := sig) (Γ := []) Op.drp
                                (.cons (Term.op (S := sig) (Γ := []) Op.quo
                                  (.cons nilP .nil)) .nil) at source
                            have outerArgs := eq_of_heq (Term.op.inj source).2
                            have names := (Args.cons.inj outerArgs).1
                            have innerArgs := eq_of_heq (Term.op.inj names).2
                            exact (Args.cons.inj innerArgs).1
                          have innerLinear : holeCount inner = 1 := by
                            simpa [holeCount, countVar, countVarArgs,
                              weakenVar] using linear
                          exact nil_does_not_step_in_context
                            (inst inner b)
                            ⟨inner, a, b, innerLinear, fires,
                              innerSource, rfl⟩

/-- The separate Drop rule, with one ordinary process variable and a root
position. It acts on the same signature, metas and equations as the local
communication profile. -/
def dropRule : PositionedRewrite schemaSig where
  ctx := [Srt.pr]
  sort := Srt.pr
  lhs := .op (Sum.inl Op.drp)
    (.cons (.op (Sum.inl Op.quo) (.cons (.var .zero) .nil)) .nil)
  rhs := .var .zero
  position :=
    { carrier := Srt.pr
      ctxt := .var .zero
      redex := .op (Sum.inl Op.drp)
        (.cons (.op (Sum.inl Op.quo) (.cons (.var .zero) .nil)) .nil)
      plugs := rfl
      linear := rfl }

/-- Add Drop as a separately named operational profile over the same
equation presentation. -/
def rhoWithDrop : Presentation sig where
  metas := metas
  eqs := rhoE
  rules := [comm, dropRule]

/-- Adding Drop leaves the authored equation component exactly unchanged. -/
theorem equations_unchanged : rhoWithDrop.eqs = rho.eqs := rfl

/-- Thus it is conservative for equational provability, although the theorem
below shows it is not conservative for operational steps. -/
theorem equational_theory_unchanged
    {Γ : Ctx sig} {sort : Srt}
    {left right : Term sig Γ sort} :
    EqClosure rhoWithDrop.eqs left right ↔
      EqClosure rho.eqs left right := Iff.rfl

/-- The old communication steps remain steps of the extended profile. -/
theorem comm_step_in_rhoWithDrop
    {sort : Srt} {source target : Term sig [] sort}
    (h : rho.Step source target) : rhoWithDrop.Step source target := by
  rcases h with ⟨i, fires⟩
  have index : i = (⟨0, by decide⟩ : Fin rho.rules.length) := by
    apply Fin.ext
    change i.val = 0
    have limit : i.val < 1 := by simpa [rho] using i.isLt
    omega
  subst index
  exact ⟨⟨0, by decide⟩, fires⟩

/-- Drop fires in the extended profile on the closed null process. -/
theorem drop_step_in_rhoWithDrop :
    rhoWithDrop.Step dropQuotedNil nilP := by
  let witness : RuleInstance metas dropRule :=
    { body := contDiscard
      close := fun _ v => match v with
        | .zero => nilP }
  refine ⟨⟨1, by decide⟩, ?_⟩
  exact step_of_rootStep dropRule (rootStep_of_instance dropRule witness)

/-- The extension is not conservative for the one-step relation on the
existing closed process language. -/
theorem drop_extension_changes_steps :
    rhoWithDrop.Step dropQuotedNil nilP ∧
      ¬ rho.Step dropQuotedNil nilP := by
  constructor
  · exact drop_step_in_rhoWithDrop
  · rintro ⟨i, fires⟩
    have index : i = (⟨0, by decide⟩ : Fin rho.rules.length) := by
      apply Fin.ext
      change i.val = 0
      have limit : i.val < 1 := by simpa [rho] using i.isLt
      omega
    subst index
    exact no_comm_at_drop nilP fires

end Mettapedia.OSLF.Binding.RhoDropBoundary
