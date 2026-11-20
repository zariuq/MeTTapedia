import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.SharedAdmission

/-!
# Every firing on the shared image is an original firing

The correspondence is onto firing data, not only onto successful examples.
The added row-use witnesses have a unique constructor on shared labels. Hence
the two constructions agree on all admissions and actual successor states.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Shared

open Interface (Frames)

universe uO uT uH uE uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : RuleSyntax.Program Tm}

def forget (s : RuleSyntax.State Tm O) (f : Firing O E (program P) (State.ofShared s)) :
    RuleSyntax.Firing O E P s.frame :=
  ⟨f.rule.basic, f.member.1, f.ext, f.opening, f.selection, f.seen⟩

theorem state_injective : Function.Injective (State.ofShared (Tm := Tm) (O := O)) := by
  intro first second same
  cases first with
  | mk a knowledge present label =>
    cases second with
    | mk b otherKnowledge otherPresent otherLabel =>
      have frame : a = b := congrArg State.frame same
      cases frame
      simp only [State.ofShared, State.mk.injEq, heq_eq_eq, true_and] at same
      obtain ⟨known, rows, values⟩ := same
      have labels : label = otherLabel := funext fun o => Row.shared.inj (congrFun values o)
      cases known
      cases rows
      cases labels
      rfl

theorem forget_lift (s : RuleSyntax.State Tm O) (f : RuleSyntax.Firing O E P s.frame) :
    forget s (lift s f) = f := rfl

theorem lift_forget (s : RuleSyntax.State Tm O) (f : Firing O E (program P) (State.ofShared s)) :
    lift s (forget s f) = f := by
  cases f with
  | mk rowRule member extension opening selection taken read seen =>
    cases rowRule with
    | mk basic schemas =>
      have empty : schemas = [] := member.2
      subst schemas
      have takeWitnesses : taken = (fun i => RowUse.shared (s.label (selection.taken.get i))) := by
        funext i
        cases taken i
        rfl
      have readWitnesses : read = (fun i => RowUse.shared (s.label (selection.read.get i))) := by
        funext i
        cases read i
        rfl
      subst taken
      subst read
      rfl

theorem firing_bijection (s : RuleSyntax.State Tm O) :
    Function.Bijective (lift (E := E) (P := P) s) := by
  constructor
  · intro first second same
    have projected := congrArg (forget s) same
    simpa only [forget_lift] using projected
  · intro f
    exact ⟨forget s f, lift_forget s f⟩

variable [DecidableEq O]

theorem forget_admits_iff (X : Frames Tm Hom) (s : RuleSyntax.State Tm O)
    (f : Firing O E (program P) (State.ofShared s)) :
    (forget s f).Admits X s ↔ f.Admits X := by
  have comparison := admits_iff X s (forget s f)
  rw [lift_forget] at comparison
  exact comparison.symm

theorem forget_result (X : Frames Tm Hom) (s : RuleSyntax.State Tm O)
    (f : Firing O E (program P) (State.ofShared s)) :
    State.ofShared ((forget s f).result X s) = f.result X := by
  have comparison := result_eq X s (forget s f)
  rw [lift_forget] at comparison
  exact comparison.symm

/-- There are no additional transitions escaping the shared-row image. -/
theorem shared_successor (X : Frames Tm Hom) (s : RuleSyntax.State Tm O)
    (f : Firing O E (program P) (State.ofShared s)) (admitted : f.Admits X) :
    ∃ original : RuleSyntax.Firing O E P s.frame,
      original.Admits X s ∧ lift s original = f ∧
        State.ofShared (original.result X s) = f.result X :=
  ⟨forget s f, (forget_admits_iff X s f).mpr admitted, lift_forget s f, forget_result X s f⟩

#print axioms lift_forget
#print axioms state_injective
#print axioms firing_bijection
#print axioms forget_admits_iff
#print axioms forget_result
#print axioms shared_successor

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Shared
