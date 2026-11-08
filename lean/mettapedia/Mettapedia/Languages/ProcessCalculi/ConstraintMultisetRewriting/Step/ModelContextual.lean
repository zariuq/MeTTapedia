import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ModelHenkin
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ContextualDiamond

/-!
# The contextual step in set models

**Set algebras of a binding signature** (`SetSemantics.SetAlgebra`): a set for every sort, and for
every operator a function of its arguments, where an argument that binds the sorts `bs` is read as a
function of their values. Terms evaluate in an environment of their context (`eval`); renaming and
substitution are evaluation in the renamed and substituted environment (`eval_rename`, `eval_bind`):
the substitution lemma.

**Points of a declaration frame** (`Point`): every metavariable of arity `(Γ, s)` denotes a function
from values of `Γ` to values of `s`. A point extends the algebra to the frame's signature (`extend`),
and contextual instantiation is evaluation at the pulled-back point (`eval_instantiate`): a
metavariable occurrence is its denotation applied to the values of its arguments.

**The set model of the contextual frames** (`contextualSetModel`) is a Henkin model of
`Frames.contextual S`: a term observation evaluates to its context, its sort and the function it
denotes. With inhabited sorts every frame has a point (`point_inhabited`), so **every admitted firing
of every step over contextual frames has a set point of its information** (`contextual_realized`),
the step's transitions pull set points back (`Step.model_transition`) and runs map functorially
(`Step.eval_pullRun_append`). The helper step's guards are equations, written in the guard syntax
(`Helpers.helper_guardedBy`); they are positive, so they hold at every set point pulled back from a
solution (`Helpers.helper_guards_pull`).

**Control: the constructor-free swap** (`SwapControl.separates`). One sort, no operators, a binary
metavariable `M`: the equation `M(x, y) = M(y, x)` is solved symbolically by a fresh nullary helper,
has no closed solution (a closed term in context `x, y` is `x` or `y`), and has a point in the set
model on a one-element sort. Set points with inhabited sorts exist where the closed term model has
none.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

universe u uOcc uS uF

namespace SetSemantics

section Algebra

variable {T : Signature}

/-- Values of the variables of a context. -/
abbrev Env {Srt : Type} (D : Srt → Type u) (Γ : List Srt) : Type u := (s : Srt) → Var Γ s → D s

/-- The empty environment. -/
def emptyEnv {Srt : Type} (D : Srt → Type u) : Env D [] := fun _ v => nomatch v

/-- Values of bound variables in front of an environment. -/
def appendEnv {Srt : Type} {D : Srt → Type u} : {bs : List Srt} → {Γ : List Srt} → Env D bs → Env D Γ →
    Env D (bs ++ Γ)
  | [], _, _, ρ => ρ
  | _ :: _, _, η, ρ => fun _ v => match v with
      | .zero => η _ .zero
      | .succ w => appendEnv (fun _ w' => η _ (.succ w')) ρ _ w

/-- The values of an operator's arguments: an argument binding `bs` is a function of their values. -/
def ArgValues {Srt : Type} (D : Srt → Type u) : List (List Srt × Srt) → Type u
  | [] => PUnit
  | (bs, s) :: as => (Env D bs → D s) × ArgValues D as

/-- **A set algebra of a binding signature.** -/
structure SetAlgebra (T : Signature) where
  carrier : T.Srt → Type u
  op : {s : T.Srt} → (o : T.Op s) → ArgValues carrier (T.arity o) → carrier s

variable (A : SetAlgebra.{u} T)

mutual

/-- **Evaluation** of a term in an environment of its context. -/
def eval : {Γ : Ctx T} → {s : T.Srt} → Term T Γ s → Env A.carrier Γ → A.carrier s
  | _, _, .var v, ρ => ρ _ v
  | _, _, .op o args, ρ => A.op o (evalArgs args ρ)

def evalArgs : {as : List (List T.Srt × T.Srt)} → {Γ : Ctx T} → Args T as Γ → Env A.carrier Γ →
    ArgValues A.carrier as
  | _, _, .nil, _ => PUnit.unit
  | _, _, .cons head tail, ρ => (fun η => eval head (appendEnv η ρ), evalArgs tail ρ)

end

theorem appendEnv_liftRen {Γ Δ : Ctx T} (ρ : Env A.carrier Δ) (r : Ren T Γ Δ) :
    ∀ (bs : List T.Srt) (η : Env A.carrier bs) (s : T.Srt) (v : Var (bs ++ Γ) s),
      appendEnv η ρ s (liftRen r bs s v) = appendEnv η (fun s v => ρ s (r s v)) s v
  | [], _, _, _ => rfl
  | _ :: _, _, _, .zero => rfl
  | _ :: bs, η, s, .succ w => appendEnv_liftRen ρ r bs (fun _ w' => η _ (.succ w')) s w

mutual

/-- **Renaming is evaluation in the renamed environment.** -/
theorem eval_rename : ∀ {Γ Δ : Ctx T} {s : T.Srt} (r : Ren T Γ Δ) (t : Term T Γ s)
    (ρ : Env A.carrier Δ), eval A (rename r t) ρ = eval A t (fun s v => ρ s (r s v))
  | _, _, _, _, .var _, _ => rfl
  | _, _, _, r, .op o args, ρ => congrArg (A.op o) (evalArgs_renameArgs r args ρ)

theorem evalArgs_renameArgs : ∀ {as : List (List T.Srt × T.Srt)} {Γ Δ : Ctx T} (r : Ren T Γ Δ)
    (args : Args T as Γ) (ρ : Env A.carrier Δ),
    evalArgs A (renameArgs r args) ρ = evalArgs A args (fun s v => ρ s (r s v))
  | _, _, _, _, .nil, _ => rfl
  | _, _, _, r, .cons (bs := bs) head tail, ρ =>
      Prod.ext
        (funext fun η => (eval_rename (liftRen r bs) head (appendEnv η ρ)).trans
          (congrArg (eval A head) (funext fun s => funext fun v => appendEnv_liftRen A ρ r bs η s v)))
        (evalArgs_renameArgs r tail ρ)

end

theorem eval_liftSub {Γ Δ : Ctx T} (σ : Sub T Γ Δ) (ρ : Env A.carrier Δ) :
    ∀ (bs : List T.Srt) (η : Env A.carrier bs) (s : T.Srt) (v : Var (bs ++ Γ) s),
      eval A (liftSub σ bs s v) (appendEnv η ρ) = appendEnv η (fun s v => eval A (σ s v) ρ) s v
  | [], _, _, _ => rfl
  | _ :: _, _, _, .zero => rfl
  | _ :: bs, η, s, .succ w => by
      show eval A (rename (fun _ v => .succ v) (liftSub σ bs s w)) (appendEnv η ρ) = _
      rw [eval_rename]
      exact eval_liftSub σ ρ bs (fun _ w' => η _ (.succ w')) s w

mutual

/-- **The substitution lemma**: substitution is evaluation in the substituted environment. -/
theorem eval_bind : ∀ {Γ Δ : Ctx T} {s : T.Srt} (σ : Sub T Γ Δ) (t : Term T Γ s)
    (ρ : Env A.carrier Δ), eval A (bind σ t) ρ = eval A t (fun s v => eval A (σ s v) ρ)
  | _, _, _, _, .var _, _ => rfl
  | _, _, _, σ, .op o args, ρ => congrArg (A.op o) (evalArgs_bindArgs σ args ρ)

theorem evalArgs_bindArgs : ∀ {as : List (List T.Srt × T.Srt)} {Γ Δ : Ctx T} (σ : Sub T Γ Δ)
    (args : Args T as Γ) (ρ : Env A.carrier Δ),
    evalArgs A (bindArgs σ args) ρ = evalArgs A args (fun s v => eval A (σ s v) ρ)
  | _, _, _, _, .nil, _ => rfl
  | _, _, _, σ, .cons (bs := bs) head tail, ρ =>
      Prod.ext
        (funext fun η => (eval_bind (liftSub σ bs) head (appendEnv η ρ)).trans
          (congrArg (eval A head) (funext fun s => funext fun v => eval_liftSub A σ ρ bs η s v)))
        (evalArgs_bindArgs σ tail ρ)

end

/-- First-order argument values, read as an environment of the parameters. -/
def argEnv {Srt : Type} {D : Srt → Type u} : {bs : List Srt} → ArgValues D (bs.map (fun b => ([], b))) →
    Env D bs
  | [], _ => fun _ v => nomatch v
  | _ :: _, values => fun _ v => match v with
      | .zero => values.1 (emptyEnv D)
      | .succ w => argEnv values.2 _ w

/-- Arguments read as a substitution evaluate to their values. -/
theorem eval_argsToSub : ∀ {bs : List T.Srt} {Γ : Ctx T} (args : Args T (bs.map (fun b => ([], b))) Γ)
    (ρ : Env A.carrier Γ), (fun s v => eval A (argsToSub args s v) ρ) = argEnv (evalArgs A args ρ)
  | [], _, .nil, _ => funext fun _ => funext fun v => nomatch v
  | _ :: _, _, .cons _ tail, ρ => funext fun s => funext fun v => by
      cases v with
      | zero => rfl
      | succ w => exact congrFun (congrFun (eval_argsToSub tail ρ) s) w

end Algebra

/-! ## Points of declaration frames -/

variable {S : Signature} (A : SetAlgebra.{u} S)

/-- **A point of a declaration family**: every metavariable denotes a function of its parameters. -/
abbrev Point {V : Type} (declaration : V → MetaArity S) : Type u :=
  (m : V) → Env A.carrier (declaration m).1 → A.carrier (declaration m).2

/-- A point extends the algebra to the frame's signature. -/
abbrev extend {V : Type} (declaration : V → MetaArity S) (p : Point A declaration) :
    SetAlgebra.{u} (signature S declaration) where
  carrier := A.carrier
  op
    | .inl o, args => A.op o args
    | .inr (.mk m), args => p m (argEnv args)

/-- Pull a point back along an assignment: each metavariable denotes its image, evaluated. -/
def pullPoint {V W : Type} {source : V → MetaArity S} {target : W → MetaArity S}
    (σ : Assignment source target) (q : Point A target) : Point A source :=
  fun m γ => eval (extend A target q) (σ m) γ

variable {V W : Type} {source : V → MetaArity S} {target : W → MetaArity S}

mutual

/-- **Instantiation is evaluation at the pulled-back point.** -/
theorem eval_instantiate (σ : Assignment source target) (q : Point A target) :
    ∀ {Γ : Ctx S} {s : S.Srt} (t : Term (signature S source) Γ s) (ρ : Env A.carrier Γ),
      eval (extend A target q) (instantiate σ t) ρ = eval (extend A source (pullPoint A σ q)) t ρ
  | _, _, .var _, _ => rfl
  | _, _, .op (.inl o) args, ρ => congrArg (A.op o) (evalArgs_instantiateArgs σ q args ρ)
  | _, _, .op (.inr (.mk m)) args, ρ => by
      show eval (extend A target q) (bind (argsToSub (instantiateArgs σ args)) (σ m)) ρ =
        eval (extend A target q) (σ m) (argEnv (evalArgs (extend A source (pullPoint A σ q)) args ρ))
      rw [eval_bind, eval_argsToSub, evalArgs_instantiateArgs σ q args ρ]

theorem evalArgs_instantiateArgs (σ : Assignment source target) (q : Point A target) :
    ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx S} (args : Args (signature S source) as Γ)
      (ρ : Env A.carrier Γ),
      evalArgs (extend A target q) (instantiateArgs σ args) ρ =
        evalArgs (extend A source (pullPoint A σ q)) args ρ
  | _, _, .nil, _ => rfl
  | _, _, .cons head tail, ρ =>
      Prod.ext (funext fun η => eval_instantiate σ q head (appendEnv η ρ))
        (evalArgs_instantiateArgs σ q tail ρ)

end

/-- **The set model of the contextual frames.** A term observation evaluates to its context, its
sort and the function it denotes; points are points of the frame; pulling back is `pullPoint`. -/
def contextualSetModel :
    (Frames.contextual S).HenkinModel (Σ (Γ : Ctx S) (s : S.Srt), Env A.carrier Γ → A.carrier s)
      (fun F => Point A F.arity) where
  eval t p := ⟨t.1, t.2.1, fun ρ => eval (extend A _ p) t.2.2 ρ⟩
  pull σ q := pullPoint A σ q
  eval_act σ t q := by
    rcases t with ⟨Γ, s, t⟩
    show (⟨Γ, s, fun ρ => eval (extend A _ q) (instantiate σ t) ρ⟩ :
        Σ (Γ : Ctx S) (s : S.Srt), Env A.carrier Γ → A.carrier s) =
      ⟨Γ, s, fun ρ => eval (extend A _ (pullPoint A σ q)) t ρ⟩
    exact congrArg (fun g => (⟨Γ, s, g⟩ : Σ (Γ : Ctx S) (s : S.Srt), Env A.carrier Γ → A.carrier s))
      (funext fun ρ => eval_instantiate A σ q t ρ)
  eval_E same _ := by
    cases same
    rfl

/-- **With inhabited sorts every frame has a point.** -/
theorem point_inhabited (inhabited : ∀ s : S.Srt, Nonempty (A.carrier s)) (F : Frames.Frame S) :
    Nonempty (Point A F.arity) :=
  ⟨fun m _ => Classical.choice (inhabited (F.arity m).2)⟩

/-- **Every admitted firing of every step over contextual frames has a set point of its information**,
in every set algebra with inhabited sorts. -/
theorem contextual_realized (inhabited : ∀ s : S.Srt, Nonempty (A.carrier s)) {O : Type uOcc}
    [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
    (P : Step (Frames.contextual S) O State Firing) {s : State} {f : Firing s} (admitted : P.Admits f) :
    ∃ q : Point A (P.target f).arity, (contextualSetModel A).Models q (P.information f) :=
  P.realized (contextualSetModel A) (point_inhabited A inhabited) admitted

end SetSemantics

/-! ## The helper step's guards are equations -/

namespace GuardFormula

universe uT

variable {T : Type uT} {O : Type uOcc}

/-- The conjunction of the equations of a store. -/
def equations : EquationStore T → GuardFormula T O
  | [] => .top
  | e :: rest => .and (.eq e.1 e.2) (equations rest)

theorem sat_equations (R : T → T → Prop) :
    ∀ store : EquationStore T, (equations (O := O) store).Sat R ↔ ∀ e ∈ store, R e.1 e.2
  | [] => by simp [equations, Sat]
  | e :: rest => by
      rw [List.forall_mem_cons, ← sat_equations R rest]
      exact Iff.rfl

theorem equations_positive : ∀ store : EquationStore T, (equations (O := O) store).Positive
  | [] => .top
  | e :: rest => .and (.eq e.1 e.2) (equations_positive rest)

end GuardFormula

namespace Helpers

variable {S : Signature} {O : Type} [DecidableEq O]

/-- The guard of a helper firing: its equations, carried into the extended frame. -/
def helperGuard {s : State S O} (f : Firing s) :
    GuardFormula (Observation S (extend s.frame f.helper).arity) O :=
  GuardFormula.equations ((Frames.contextual S).applyStore (incl s.frame f.helper) f.guards)

/-- **The helper step is in the guard fibre.** -/
theorem helper_guardedBy : (helperStep (S := S) (O := O)).GuardedBy helperGuard := by
  intro s f b σ
  show (Frames.contextual S).Models (Assignment.compose σ (incl s.frame f.helper)) f.guards ↔
    (GuardFormula.equations ((Frames.contextual S).applyStore (incl s.frame f.helper) f.guards)).Sat
      ((Frames.contextual S).kernel σ)
  rw [GuardFormula.sat_equations]
  exact (Frames.models_applyStore (X := Frames.contextual S) (incl s.frame f.helper) σ f.guards).symm

/-- **Helper guards hold at every set point pulled back from a solution.** -/
theorem helper_guards_pull (A : SetSemantics.SetAlgebra.{u} S) {s : State S O} (f : Firing s)
    {b : Frames.Frame S} {σ : Assignment (extend s.frame f.helper).arity b.arity}
    (held : (helperStep (S := S) (O := O)).Holds f b σ) (r : SetSemantics.Point A b.arity) :
    (SetSemantics.contextualSetModel A).Satisfies (SetSemantics.pullPoint A σ r) (helperGuard f) :=
  Frames.HenkinModel.satisfies_pull_of_positive (M := SetSemantics.contextualSetModel A)
    (GuardFormula.equations_positive _)
    ((helper_guardedBy f b σ).mp held) r

end Helpers

/-! ## Control: the constructor-free swap -/

namespace SwapControl

open SetSemantics

/-- One sort and no operators. -/
abbrev bare : Signature where
  Srt := Unit
  Op _ := Empty
  arity o := o.elim

/-- The frame with one binary metavariable `M`. -/
abbrev binary : Frames.Frame bare := ⟨Unit, fun _ => ([(), ()], ())⟩

/-- The closed frame: no metavariables. -/
abbrev closed : Frames.Frame bare := ⟨Empty, Empty.elim⟩

/-- The frame with one nullary helper `H`. -/
abbrev helper : Frames.Frame bare := ⟨Unit, fun _ => ([], ())⟩

/-- The context `x, y`. -/
abbrev xy : Ctx bare := [(), ()]

/-- `M(a, b)` for variables `a`, `b` of `x, y`. -/
def app (first second : Var xy ()) : Term (signature bare binary.arity) xy () :=
  .op (.inr (.mk ())) (.cons (.var first) (.cons (.var second) .nil))

/-- `M(x, y) = M(y, x)`. -/
def swapped : EquationStore (Observation bare binary.arity) :=
  [(observe (app .zero (.succ .zero)), observe (app (.succ .zero) .zero))]

/-- `M := H`. -/
def toHelper : Assignment binary.arity helper.arity := fun _ => .op (.inr (.mk ())) .nil

theorem solvable : (Frames.contextual bare).Solvable swapped :=
  ⟨helper, toHelper, fun e member => by
    obtain rfl := List.mem_singleton.mp member
    rfl⟩

/-- A closed term in the context `x, y` is a variable. -/
theorem closed_term_var : ∀ t : Term (signature bare closed.arity) xy (), ∃ v : Var xy (), t = .var v
  | .var v => ⟨v, rfl⟩
  | .op (.inl o) _ => o.elim
  | .op (.inr (.mk m)) _ => m.elim

theorem no_closed_solution : ¬ ∃ σ : Assignment binary.arity closed.arity, (Frames.contextual bare).Models σ swapped := by
  rintro ⟨σ, solved⟩
  have equal := solved _ (List.mem_singleton_self _)
  obtain ⟨v, hv⟩ := closed_term_var (σ ())
  have inner : instantiate σ (app .zero (.succ .zero)) = instantiate σ (app (.succ .zero) .zero) :=
    observe_injective equal
  change bind (argsToSub (instantiateArgs σ _)) (σ ()) = bind (argsToSub (instantiateArgs σ _)) (σ ()) at inner
  rw [hv] at inner
  cases v with
  | zero => cases inner
  | succ w =>
      cases w with
      | zero => cases inner
      | succ w' => exact nomatch w'

/-- The one-element set algebra. -/
def unitAlgebra : SetAlgebra.{0} bare where
  carrier _ := Unit
  op o _ := o.elim

/-- **The constructor-free swap**: solvable symbolically, no closed solution, and a set point. -/
theorem separates :
    (Frames.contextual bare).Solvable swapped ∧
      (¬ ∃ σ : Assignment binary.arity closed.arity, (Frames.contextual bare).Models σ swapped) ∧
      (contextualSetModel unitAlgebra).Models (fun _ _ => ()) swapped :=
  ⟨solvable, no_closed_solution, fun e member => by
    obtain rfl := List.mem_singleton.mp member
    rfl⟩

end SwapControl

#print axioms SetSemantics.eval_rename
#print axioms SetSemantics.eval_bind
#print axioms SetSemantics.eval_argsToSub
#print axioms SetSemantics.eval_instantiate
#print axioms SetSemantics.contextualSetModel
#print axioms SetSemantics.point_inhabited
#print axioms SetSemantics.contextual_realized
#print axioms GuardFormula.sat_equations
#print axioms Helpers.helper_guardedBy
#print axioms Helpers.helper_guards_pull
#print axioms SwapControl.no_closed_solution
#print axioms SwapControl.separates

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
