import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrame
import Lean.Elab.Tactic.Omega

/-!
# Contextual holes, symbolic aliases and rigid object variables

All terms are the existing intrinsically scoped binding terms. Reordered,
repeated and compound arguments are legal. Repetition can lose inverse
uniqueness. A hole may refer to a bound variable through a declared argument;
a nullary hole cannot capture it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrame.Controls

open Mettapedia.OSLF.Binding

inductive Operator where
  | pair
  | lam
  | constant
  deriving DecidableEq

def signature : Signature where
  Srt := Unit
  Op _ := Operator
  arity operator := match operator with
    | .pair => [([], ()), ([], ())]
    | .lam => [([()], ())]
    | .constant => []

abbrev metas : List (MetaArity signature) :=
  [([(), ()], ()), ([()], ()), ([], ()), ([], ())]

abbrev extended := withMetas signature metas

def pId : Fin metas.length := ⟨0, by decide⟩
def bId : Fin metas.length := ⟨1, by decide⟩
def uId : Fin metas.length := ⟨2, by decide⟩
def vId : Fin metas.length := ⟨3, by decide⟩

def pair {Γ : Ctx signature} (left right : Term extended Γ ()) : Term extended Γ () :=
  .op (.inl .pair) (.cons left (.cons right .nil))

def pCall {Γ : Ctx signature} (left right : Term extended Γ ()) : Term extended Γ () :=
  .op (.inr (.mk pId)) (.cons left (.cons right .nil))

def bCall {Γ : Ctx signature} (argument : Term extended Γ ()) : Term extended Γ () :=
  .op (.inr (.mk bId)) (.cons argument .nil)

def u {Γ : Ctx signature} : Term extended Γ () := .op (.inr (.mk uId)) .nil
def v {Γ : Ctx signature} : Term extended Γ () := .op (.inr (.mk vId)) .nil

def bodies : Assignment signature metas
  | ⟨0, _⟩ => pair (.var .zero) (.var (.succ .zero))
  | ⟨1, _⟩ => .var .zero
  | ⟨2, _⟩ => v
  | ⟨3, _⟩ => v
  | ⟨n + 4, impossible⟩ => by
    have bound : n + 4 < 4 := impossible
    omega

def chooseFirst : Assignment signature metas
  | ⟨0, _⟩ => .var .zero
  | ⟨1, _⟩ => .var .zero
  | ⟨2, _⟩ => v
  | ⟨3, _⟩ => v
  | ⟨n + 4, impossible⟩ => by
    have bound : n + 4 < 4 := impossible
    omega

def chooseSecond : Assignment signature metas
  | ⟨0, _⟩ => .var (.succ .zero)
  | ⟨1, _⟩ => .var .zero
  | ⟨2, _⟩ => v
  | ⟨3, _⟩ => v
  | ⟨n + 4, impossible⟩ => by
    have bound : n + 4 < 4 := impossible
    omega

abbrev A (Γ : Ctx signature) := action signature metas Γ ()

theorem swapped_spine_is_accepted :
    (A [(), ()]).apply bodies (pCall (.var (.succ .zero)) (.var .zero)) =
      pair (.var (.succ .zero)) (.var .zero) := rfl

theorem repeated_arguments_are_accepted :
    (A [()]).apply bodies (pCall (.var .zero) (.var .zero)) =
      pair (.var .zero) (.var .zero) := rfl

theorem compound_arguments_are_accepted :
    (A [(), ()]).apply bodies
      (pCall (pair (.var .zero) (.var (.succ .zero))) (.var .zero)) =
      pair (pair (.var .zero) (.var (.succ .zero))) (.var .zero) := rfl

theorem declared_argument_can_refer_to_bound_variable :
    (A [()]).Consistent [(bCall (.var .zero), Term.var .zero)] := by
  refine ⟨bodies, ?_⟩
  intro equation member
  have same : equation = (bCall (Term.var .zero), (Term.var .zero : Term extended [()] ())) := by
    simpa using member
  subst equation
  rfl

theorem symbolic_variable_against_variable_is_accepted :
    (A []).Consistent [(u, v)] := by
  refine ⟨bodies, ?_⟩
  intro equation member
  have same : equation = (u (Γ := []), v (Γ := [])) := by simpa using member
  subst equation
  rfl

theorem repeated_arguments_do_not_determine_the_assignment :
    chooseFirst ≠ chooseSecond ∧
      (A [()]).apply chooseFirst (pCall (.var .zero) (.var .zero)) =
        (A [()]).apply chooseSecond (pCall (.var .zero) (.var .zero)) := by
  constructor
  · intro same
    have images := congrFun same pId
    change (Term.var (S := extended) (Γ := [(), ()]) .zero) = .var (.succ .zero) at images
    have positions := Term.var.inj images
    cases positions
  · rfl

/-- The image of a nullary hole has empty object context, so inserting it
under a binder cannot turn it into that binder's variable. -/
private theorem bind_empty_ne_var {S : Signature} {Γ : Ctx S} {sort : S.Srt}
    (body : Term S [] sort) (substitution : Sub S [] Γ) (position : Var Γ sort) :
    bind substitution body ≠ Term.var position := by
  cases body with
  | var impossible => cases impossible
  | op operator arguments => intro same; cases same

theorem nullary_hole_cannot_capture_bound_variable :
    ¬ (A [()]).Consistent [(u, Term.var .zero)] := by
  rintro ⟨assignment, solved⟩
  have same := solved (u, Term.var .zero) (by simp)
  change bind (S := extended) (argsToSub (S := extended) (bs := []) (Γ := [()])
      (Args.nil (S := extended) (Γ := [()])))
    (assignment uId) = Term.var (S := extended) .zero at same
  exact bind_empty_ne_var (assignment uId) _ _ same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrame.Controls
