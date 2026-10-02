import Mettapedia.OSLF.Syntax.BindingSignature
import Mettapedia.OSLF.Syntax.PresentationSemantics

/-!
# The reflective calculus as a binding signature, and its communication schema

The signature declares binding where binding happens: the input former opens
its continuation under the name it receives, and nothing else binds.  There is
no separate abstraction constructor, and no separate substitution: the
continuation is instantiated by the substitution of the term algebra.

The communication rule quantifies over a continuation, which is a process open
in one name.  That is a *metavariable of arity `([nm], pr)`*, not a first-order
variable.  Chapter 19's worked example gives that position the carrier
`[Nm -> Pr]`, an exponential, which is why Section 7.6 must equip the
classifying theory with cartesian closed structure.  Adjoining a metavariable
of the corresponding binding arity achieves the same expressiveness without
requiring the object language to carry function sorts it does not otherwise
have: processes are not functions, and only the *rule* needs to range over an
abstraction.

Because metavariables are adjoined as operators, the schema is an ordinary
term of an extended signature, and renaming, substitution and all their laws
apply to it unchanged.

The rule is recorded with its redex position, as a `PositionedRewrite`, so the
data the generator reads is the data the rule supplies.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

namespace RhoSchema

/-- The two sorts of the reflective calculus: names and processes. -/
inductive Srt where
  | nm
  | pr
  deriving DecidableEq, Repr

/-- The term formers.  `inp` is the only one that binds: its continuation is
opened under the name it receives. -/
inductive Op : Srt → Type where
  | nil : Op Srt.pr
  | par : Op Srt.pr
  | out : Op Srt.pr
  | inp : Op Srt.pr
  | quo : Op Srt.nm
  | drp : Op Srt.pr

/-- The signature of the reflective calculus.  Binding is declared here, in
`inp`'s second argument, rather than by a dedicated lambda constructor. -/
abbrev sig : Signature where
  Srt := Srt
  Op := Op
  arity := fun {_} o => match o with
    | .nil => []
    | .par => [([], Srt.pr), ([], Srt.pr)]
    | .out => [([], Srt.nm), ([], Srt.pr)]
    | .inp => [([], Srt.nm), ([Srt.nm], Srt.pr)]
    | .quo => [([], Srt.pr)]
    | .drp => [([], Srt.nm)]

/-- The communication rule quantifies over a *continuation*, which is a process
open in one name.  That is a metavariable of arity `([nm], pr)`; it is not a
first-order variable, and making it one would require the object language to
carry function sorts it does not otherwise need. -/
abbrev metas : List (MetaArity sig) := [([Srt.nm], Srt.pr)]

/-- The signature in which the rule schema is written. -/
abbrev schemaSig : Signature := withMetas sig metas

/-- The rule's first-order variables: a channel and an emitted process. -/
abbrev G : Ctx schemaSig := [Srt.nm, Srt.pr]

/-- The continuation metavariable, applied to a name. -/
abbrev cont {Γ : Ctx schemaSig} (a : Term schemaSig Γ Srt.nm) :
    Term schemaSig Γ Srt.pr :=
  Term.op (S := schemaSig) (Sum.inr (MetaOp.mk (M := metas) 0)) (.cons a .nil)

/-- `n!(q) | for(y <- n) K[y]` -- the left-hand side of communication. -/
def commLhs : Term schemaSig G Srt.pr :=
  Term.op (S := schemaSig) (Sum.inl Op.par)
    (.cons
      (Term.op (S := schemaSig) (Sum.inl Op.out)
        (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil)))
      (.cons
        (Term.op (S := schemaSig) (Sum.inl Op.inp)
          (.cons (.var .zero) (.cons (cont (.var .zero)) .nil)))
        .nil))

/-- `K[@q]` -- the continuation instantiated at the quoted payload. -/
def commRhs : Term schemaSig G Srt.pr :=
  cont (Term.op (S := schemaSig) (Sum.inl Op.quo) (.cons (.var (.succ .zero)) .nil))

/-- The redex position at the emitted payload: carrier `pr`, redex `q`. -/
def payloadPosition : LinearRedexPosition schemaSig G Srt.pr commLhs where
  carrier := Srt.pr
  ctxt :=
    Term.op (S := schemaSig) (Sum.inl Op.par)
      (.cons
        (Term.op (S := schemaSig) (Sum.inl Op.out)
          (.cons (.var (.succ .zero)) (.cons (.var .zero) .nil)))
        (.cons
          (Term.op (S := schemaSig) (Sum.inl Op.inp)
            (.cons (.var (.succ .zero)) (.cons (cont (.var .zero)) .nil)))
          .nil))
  redex := .var (.succ .zero)
  plugs := rfl
  linear := rfl

/-- The communication rule, with its position, as the generator's input. -/
abbrev comm : PositionedRewrite schemaSig where
  ctx := G
  sort := Srt.pr
  lhs := commLhs
  rhs := commRhs
  position := payloadPosition

/-- The hole occurs exactly once in the communication context. -/
theorem comm_hole_occurs : holeCount comm.position.ctxt = 1 := comm.position.linear

/-- The carrier of the modality generated at this position is `pr`. -/
theorem comm_carrier : comm.carrier = Srt.pr := rfl

/-- The channel is a rely parameter: the context uses it (twice, once on each
side of the cut) and the redex does not. -/
theorem channel_is_rely :
    comm.RelyParameter (Var.zero : Var G Srt.nm) := by
  constructor
  · decide
  · decide

/-- The payload variable is a local parameter: it is the redex, and the context
does not mention it. -/
theorem payload_is_local :
    comm.LocalParameter (Var.succ Var.zero : Var G Srt.pr) := by
  constructor
  · decide
  · decide

/-- The two families do not overlap at the channel. -/
theorem channel_not_local :
    ¬ comm.LocalParameter (Var.zero : Var G Srt.nm) :=
  comm.rely_not_local _ channel_is_rely

/-! ### The schema is not a ground reaction -/

/-- The left-hand side mentions the continuation metavariable, so this rule
quantifies over all continuations rather than fixing one. -/
theorem commLhs_is_a_schema : usesMeta commLhs = true := rfl

/-- So does the right-hand side: the continuation is what the rule transports. -/
theorem commRhs_is_a_schema : usesMeta commRhs = true := rfl

/-- The same communication rule can select the entire left-hand side instead
of the payload. Both are legitimate positions, but later generated modalities
read different selected data from them. -/
def commAtRoot : PositionedRewrite schemaSig where
  ctx := G
  sort := Srt.pr
  lhs := commLhs
  rhs := commRhs
  position :=
    { carrier := Srt.pr
      ctxt := .var .zero
      redex := commLhs
      plugs := rfl
      linear := rfl }

/-- Forgetting position identifies the two choices of focus. -/
theorem commAtRoot_unpositioned_eq :
    commAtRoot.unpositioned = comm.unpositioned := rfl

/-- The two positioned rules are genuinely different despite that equality. -/
theorem commAtRoot_ne_comm : commAtRoot ≠ comm := by
  intro equality
  have focusEqual := congrArg
    (fun rule : PositionedRewrite schemaSig => usesMeta rule.position.redex) equality
  change usesMeta commLhs = usesMeta payloadPosition.redex at focusEqual
  rw [commLhs_is_a_schema] at focusEqual
  cases focusEqual

/-- Operationally the two choices are indistinguishable before a construction
asks which position was selected. -/
theorem commAtRoot_step_iff_comm {s : Srt} {t u : Term sig [] s} :
    Step commAtRoot t u ↔ Step comm t u := by
  calc
    Step commAtRoot t u ↔ commAtRoot.unpositioned.Step t u :=
      commAtRoot.step_iff_unpositioned
    _ ↔ comm.unpositioned.Step t u := by rw [commAtRoot_unpositioned_eq]
    _ ↔ Step comm t u := comm.step_iff_unpositioned.symm

/-- Negative control: a ground process mentions no metavariable, so the
discriminator is not constantly `true`. -/
theorem ground_process_is_not_a_schema :
    usesMeta (Term.op (S := schemaSig) (Γ := G) (Sum.inl Op.par)
      (.cons (Term.op (S := schemaSig) (Γ := G) (Sum.inl Op.nil) .nil)
        (.cons (Term.op (S := schemaSig) (Γ := G) (Sum.inl Op.nil) .nil) .nil))) = false := rfl

/-! ### Instantiating the schema

A schema is turned into a rule by supplying a body for its metavariable.  Two
different continuations give two different rules, which is what makes this a
schema rather than one reaction wearing a variable. -/

/-- The continuation that discards the received name. -/
def contDiscard : (i : Fin metas.length) → Term sig (metas.get i).1 (metas.get i).2
  | ⟨0, _⟩ => Term.op (S := sig) Op.nil .nil

/-- The continuation that unquotes the received name. -/
def contUnquote : (i : Fin metas.length) → Term sig (metas.get i).1 (metas.get i).2
  | ⟨0, _⟩ => Term.op (S := sig) Op.drp (.cons (.var .zero) .nil)

/-- Discarding the continuation reduces the right-hand side to the null process. -/
theorem rhs_under_discard :
    instantiate contDiscard commRhs = Term.op (S := sig) (Γ := G) Op.nil .nil := rfl

/-- Unquoting it reproduces the emitted process through quote-then-drop, which
is exactly the reflective round trip the calculus is built on. -/
theorem rhs_under_unquote :
    instantiate contUnquote commRhs
      = Term.op (S := sig) (Γ := G) Op.drp
          (.cons (Term.op (S := sig) (Γ := G) Op.quo (.cons (.var (.succ .zero)) .nil)) .nil) :=
  rfl

/-- **The rule really is a schema.**  Two continuations give two different
right-hand sides, so `comm` is not one reaction in disguise. -/
theorem instantiations_differ :
    instantiate contDiscard commRhs ≠ instantiate contUnquote commRhs := by
  rw [rhs_under_discard, rhs_under_unquote]
  intro h
  injection h with _ _ ho _
  cases ho

/-! ### A closed reduction, generated by the rule -/

/-- The null process. -/
abbrev nilP : Term sig [] Srt.pr := Term.op (S := sig) (Γ := []) Op.nil .nil

/-- The only closed name available: the quote of the null process. -/
abbrev chan : Term sig [] Srt.nm :=
  Term.op (S := sig) (Γ := []) Op.quo (.cons nilP .nil)

/-- Close the rule's variables: the channel is `@0` and the payload is `0`. -/
def closeComm : Sub sig G []
  | _, .zero => chan
  | _, .succ .zero => nilP

/-- One closed instance of the communication rule: unquote the received name,
send the null process on `@0`. -/
def commInstance : RuleInstance metas comm where
  body := contUnquote
  close := closeComm

/-- The source of that instance is `@0!(0) | for(y <- @0){ *y }`. -/
theorem instance_source :
    bind closeComm (instantiate contUnquote comm.lhs)
      = Term.op (S := sig) (Γ := []) Op.par
          (.cons
            (Term.op (S := sig) (Γ := []) Op.out (.cons chan (.cons nilP .nil)))
            (.cons
              (Term.op (S := sig) (Γ := []) Op.inp
                (.cons chan
                  (.cons (Term.op (S := sig) (Γ := [Srt.nm]) Op.drp
                    (.cons (.var .zero) .nil)) .nil)))
              .nil)) :=
  rfl

/-- Its target is `*@0` -- the reflective round trip, produced by the rule and
not written by hand. -/
theorem instance_target :
    bind closeComm (instantiate contUnquote comm.rhs)
      = Term.op (S := sig) (Γ := []) Op.drp (.cons chan .nil) :=
  rfl

/-- **A genuine reduction of the reflective calculus, generated by the rule.** -/
theorem rho_communicates :
    RootStep comm
      (Term.op (S := sig) (Γ := []) Op.par
        (.cons
          (Term.op (S := sig) (Γ := []) Op.out (.cons chan (.cons nilP .nil)))
          (.cons
            (Term.op (S := sig) (Γ := []) Op.inp
              (.cons chan
                (.cons (Term.op (S := sig) (Γ := [Srt.nm]) Op.drp
                  (.cons (.var .zero) .nil)) .nil)))
            .nil)))
      (Term.op (S := sig) (Γ := []) Op.drp (.cons chan .nil)) :=
  rootStep_of_instance comm commInstance

/-- Negative control: the null process does not step.  A rule headed by
parallel composition can only fire on a term headed by parallel composition. -/
theorem nil_does_not_step (u : Term sig [] Srt.pr) :
    ¬ RootStep comm nilP u := by
  intro h
  obtain ⟨_, hI⟩ := rootStep_lhs_shape comm h
  injection hI with _ _ ho _
  cases ho

/-! ### Firing below the root -/

/-- The source of the closed instance. -/
abbrev commSource : Term sig [] Srt.pr :=
  bind closeComm (instantiate contUnquote comm.lhs)

/-- Its target. -/
abbrev commTarget : Term sig [] Srt.pr :=
  bind closeComm (instantiate contUnquote comm.rhs)

/-- The parallel context `0 | [-]`. -/
abbrev parContext : Term sig [Srt.pr] Srt.pr :=
  Term.op (S := sig) (Γ := [Srt.pr]) Op.par
    (.cons (Term.op (S := sig) (Γ := [Srt.pr]) Op.nil .nil)
      (.cons (.var .zero) .nil))

/-- It uses its hole exactly once, so it is an admissible context. -/
theorem parContext_linear : holeCount parContext = 1 := rfl

/-- **The communication fires below the root**, under a parallel remainder. -/
theorem rho_communicates_in_context :
    Step comm
      (Term.op (S := sig) (Γ := []) Op.par (.cons nilP (.cons commSource .nil)))
      (Term.op (S := sig) (Γ := []) Op.par (.cons nilP (.cons commTarget .nil))) :=
  ⟨parContext, commSource, commTarget, parContext_linear,
    rootStep_of_instance comm commInstance, rfl, rfl⟩

/-- Negative control: the null process does not step, even below the root.
Either the context is the bare hole, and then the null process would have to
step at the root, which it does not; or the context is headed by an operator,
and matching the null process forces that operator to be the null former,
whose only context has no hole at all. -/
theorem nil_does_not_step_in_context (u : Term sig [] Srt.pr) :
    ¬ Step comm nilP u := by
  rintro ⟨K, a, b, hlin, hab, hsrc, -⟩
  cases K with
  | var v =>
      cases v with
      | zero =>
          have ha : a = nilP := hsrc
          exact nil_does_not_step b (ha ▸ hab)
      | succ w => cases w
  | op f args =>
      injection hsrc with _ _ hf _
      subst hf
      cases args
      exact absurd hlin (by decide)

/-! ### The possibility generated at the payload position -/

/-- Placing the null process at the chosen position takes a step to the
reflective round trip.  The predicate is generated from the rule; only the
target predicate is supplied. -/
theorem payload_steps :
    StepsFromPosition comm
      (fun u => u = Term.op (S := sig) (Γ := []) Op.drp (.cons chan .nil)) nilP :=
  stepsFromPosition_intro commInstance rfl

/-- Negative control: the target predicate is genuinely consulted, so the
generated possibility is not constantly inhabited. -/
theorem payload_does_not_step_into_nothing :
    ¬ StepsFromPosition comm (fun _ => False) nilP := by
  rintro ⟨-, -, hF⟩
  exact hF

/-- The communication rule **separates**: every one of its variables is either
a rely parameter or a local one, so typed rely assumptions are well defined for
it.  The channel relies; the payload is local. -/
theorem comm_separated : Separated comm := by
  intro s x
  cases x with
  | zero => exact Or.inl channel_is_rely
  | succ w =>
      cases w with
      | zero => exact Or.inr payload_is_local
      | succ v => cases v

/-! ### The rely parameter, indexed -/

/-- Close the rule's variables with a chosen channel and the null payload. -/
def closeWith (n : Term sig [] Srt.nm) : Sub sig G []
  | _, .zero => n
  | _, .succ .zero => nilP

/-- **The modality generated at the payload position, with its rely parameter
indexed.**  Whatever channel the environment supplies, placing the null process
at the chosen position steps to the reflective round trip. -/
theorem payload_rely_possibly :
    RelyPossibly comm (fun _ _ _ => True)
      (fun u => u = Term.op (S := sig) (Γ := []) Op.drp (.cons chan .nil)) nilP := by
  intro env _
  refine ⟨⟨contUnquote, closeWith (env Srt.nm Var.zero channel_is_rely)⟩, ?_, rfl, rfl⟩
  intro s x hx
  cases x with
  | zero => rfl
  | succ w =>
      cases w with
      | zero => exact absurd payload_is_local (comm.rely_not_local _ hx)
      | succ v => cases v

/-- Negative control: the target predicate is consulted, so the rely-indexed
modality is not vacuously inhabited. -/
theorem payload_rely_possibly_needs_target :
    ¬ RelyPossibly comm (fun _ _ _ => True) (fun _ => False) nilP := by
  intro h
  obtain ⟨-, -, -, hF⟩ := h (relyEnvOf (closeWith chan)) (fun _ _ _ => trivial)
  exact hF

/-- The rely parameter is genuinely free: the modality holds at every channel,
which is what "rely" means -- the rule does not fix it. -/
theorem payload_steps_at_every_channel (n : Term sig [] Srt.nm) :
    ∃ I : RuleInstance metas comm,
      I.close Srt.nm Var.zero = n ∧
      bind I.close (instantiate I.body comm.position.redex) = nilP :=
  ⟨⟨contUnquote, closeWith n⟩, rfl, rfl⟩

/-! ### The structural layer on this signature -/

/-- `*@0`, a process distinct from the null process. -/
abbrev dropChan : Term sig [] Srt.pr :=
  Term.op (S := sig) (Γ := []) Op.drp (.cons chan .nil)

abbrev isNil : Pred sig [] Srt.pr := fun t => t = nilP
abbrev isDropChan : Pred sig [] Srt.pr := fun t => t = dropChan
abbrev isChan : Pred sig [] Srt.nm := fun n => n = chan

/-- The structural type at parallel composition, inhabited. -/
theorem par_structural :
    structural Op.par (.cons isNil (.cons isDropChan .nil))
      (Term.op (S := sig) (Γ := []) Op.par (.cons nilP (.cons dropChan .nil))) :=
  by refine structural_intro (S := sig) (Γ := []) Op.par ?_; simp [SatArgs]

/-- Control: the null process does not inhabit the parallel type -- the
structural layer reads the head. -/
theorem nil_not_par_structural :
    ¬ structural Op.par (.cons isNil (.cons isDropChan .nil)) nilP := by
  rintro ⟨args, ht, -⟩
  simp at ht

/-- The predicate at the continuation slot of input lives **in scope of the
received name**, so the structural layer reaches binder positions rather than
stopping at them. -/
abbrev boundIsDropped : Pred sig ([Srt.nm] ++ []) Srt.pr :=
  fun t => t = Term.op (S := sig) (Γ := [Srt.nm]) Op.drp (.cons (.var .zero) .nil)

/-- The structural type at input, inhabited -- at a binding argument. -/
theorem inp_structural :
    structural Op.inp (.cons isChan (.cons boundIsDropped .nil))
      (Term.op (S := sig) (Γ := []) Op.inp
        (.cons chan
          (.cons (Term.op (S := sig) (Γ := [Srt.nm]) Op.drp (.cons (.var .zero) .nil))
            .nil))) :=
  by refine structural_intro (S := sig) (Γ := []) Op.inp ?_; simp [SatArgs]

/-- **Without equations the interaction former splits positionally.**  Swapping
the two sides leaves the type uninhabited, so what the free signature supplies
is a positional split; the separating-conjunction reading needs the operator's
associativity and commutativity, which belong to the equations. -/
theorem par_structural_is_positional :
    ¬ structural Op.par (.cons isNil (.cons isDropChan .nil))
        (Term.op (S := sig) (Γ := []) Op.par (.cons dropChan (.cons nilP .nil))) := by
  rintro ⟨args, ht, hsat⟩
  simp only [Term.op.injEq, heq_eq_eq, true_and] at ht
  subst ht
  simp only [SatArgs, isNil] at hsat
  exact absurd hsat.1 (by simp)

/-! ### Equations, and the separating conjunction they supply -/

/-- Parallel composition, as a term former. -/
abbrev parT (a b : Term sig [] Srt.pr) : Term sig [] Srt.pr :=
  Term.op (S := sig) (Γ := []) Op.par (.cons a (.cons b .nil))

/-- Commutativity of parallel composition. -/
def commPar : EqAxiom sig metas where
  ctx := [Srt.pr, Srt.pr]
  sort := Srt.pr
  lhs := Term.op (S := schemaSig) (Sum.inl Op.par)
    (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))
  rhs := Term.op (S := schemaSig) (Sum.inl Op.par)
    (.cons (.var (.succ .zero)) (.cons (.var .zero) .nil))

/-- Associativity of parallel composition. -/
def assocPar : EqAxiom sig metas where
  ctx := [Srt.pr, Srt.pr, Srt.pr]
  sort := Srt.pr
  lhs := Term.op (S := schemaSig) (Sum.inl Op.par)
    (.cons (Term.op (S := schemaSig) (Sum.inl Op.par)
        (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil)))
      (.cons (.var (.succ (.succ .zero))) .nil))
  rhs := Term.op (S := schemaSig) (Sum.inl Op.par)
    (.cons (.var .zero)
      (.cons (Term.op (S := schemaSig) (Sum.inl Op.par)
          (.cons (.var (.succ .zero)) (.cons (.var (.succ (.succ .zero))) .nil))) .nil))

/-- The null process is the right unit of parallel composition. The left-unit
law follows from this equation and commutativity. -/
def rightUnitPar : EqAxiom sig metas where
  ctx := [Srt.pr]
  sort := Srt.pr
  lhs := Term.op (S := schemaSig) (Sum.inl Op.par)
    (.cons (.var .zero)
      (.cons (Term.op (S := schemaSig) (Sum.inl Op.nil) .nil) .nil))
  rhs := .var .zero

/-- The authored ACU equations of the reflective calculus' interaction former. -/
abbrev rhoE : List (EqAxiom sig metas) := [commPar, assocPar, rightUnitPar]

/-- **The schema is a presentation.**  Signature, equations and rules are the
three fields of one object rather than three definitions that happen to sit in
the same file, so the reflective calculus is an instance of the general
(Σ, E, R) construction and inherits everything proved about it. -/
def rho : Presentation sig where
  metas := metas
  eqs := rhoE
  rules := [comm]

/-- Its step relation is the one the rule already had. -/
theorem rho_rules : rho.rules = [comm] := rfl

/-- Its equations present parallel composition as a commutative monoid. -/
theorem rho_eqs : rho.eqs = [commPar, assocPar, rightUnitPar] := rfl

/-- Close a two-variable context. -/
def closePair (a b : Term sig [] Srt.pr) : Sub sig [Srt.pr, Srt.pr] []
  | _, .zero => a
  | _, .succ .zero => b

/-- **Parallel composition is commutative modulo the equations.** -/
theorem par_comm (a b : Term sig [] Srt.pr) :
    EqClosure rhoE (parT a b) (parT b a) :=
  EqClosure.ax_closed (E := rhoE) 0 contUnquote (closePair a b)

/-- Close the one-variable unit axiom with any process. -/
def closeOne (a : Term sig [] Srt.pr) : Sub sig [Srt.pr] []
  | _, .zero => a

/-- The right-unit law is an instance of the authored unit equation. -/
theorem par_right_unit (a : Term sig [] Srt.pr) :
    EqClosure rhoE (parT a nilP) a :=
  EqClosure.ax_closed (E := rhoE) 2 contUnquote (closeOne a)

/-- The left-unit law is derived, not an additional authored equation. -/
theorem par_left_unit (a : Term sig [] Srt.pr) :
    EqClosure rhoE (parT nilP a) a :=
  EqClosure.trans (par_comm nilP a) (par_right_unit a)

/-- Unit equality is genuinely generated by the equations; the two source
terms are not equal as raw syntax. -/
theorem par_nil_not_syntactic : parT nilP nilP ≠ nilP := by
  intro equality
  injection equality with _ _ operatorEq _
  cases operatorEq

/-- The input and output in the closed communication instance. -/
abbrev commInput : Term sig [] Srt.pr :=
  Term.op (S := sig) (Γ := []) Op.inp
    (.cons chan
      (.cons (Term.op (S := sig) (Γ := [Srt.nm]) Op.drp
        (.cons (.var .zero) .nil)) .nil))

abbrev commOutput : Term sig [] Srt.pr :=
  Term.op (S := sig) (Γ := []) Op.out (.cons chan (.cons nilP .nil))

/-- The source writes input before output. The authored rule writes the other
order; commutativity makes the two presentations agree operationally. -/
theorem input_output_communicates :
    rho.StepModE (parT commInput commOutput) commTarget := by
  apply Presentation.stepModE_resp_left (par_comm commInput commOutput)
  apply Presentation.stepModE_of_rule (i := ⟨0, by decide⟩)
  exact stepModE_of_step (E := rhoE) (step_of_rootStep comm rho_communicates)

/-- Forgetting the selected position retains the source-order communication
step in the bare unconditional presentation. -/
theorem unpositioned_input_output_communicates :
    rho.toUnpositioned.StepModE (parT commInput commOutput) commTarget :=
  (rho.stepModE_iff_toUnpositioned).mp input_output_communicates

/-- The source-order communication is a step in the extensional semantic
GSLT at the process sort. -/
theorem extensional_rho_communicates :
    (rho.toUnpositioned.toExtensionalGSLTAt Srt.pr).Step
      (parT commInput commOutput) commTarget :=
  unpositioned_input_output_communicates

/-- The source-order communication as retained event data: the authored rule
index, equation representative, context, continuation and closing substitution
are all present before erasure to the semantic step relation. -/
def rhoCommunicationEvidence :
    (rho.toUnpositioned.stepEvidenceAt Srt.pr).Evidence
      (parT commInput commOutput) commTarget :=
  ⟨⟨0, by decide⟩,
    { source' := commSource
      target' := commTarget
      before := par_comm commInput commOutput
      firing :=
        { context := Term.var Var.zero
          redex := commSource
          reduct := commTarget
          linear := rfl
          root :=
            { body := contUnquote
              close := closeComm
              source_eq := rfl
              target_eq := rfl }
          source_eq := rfl
          target_eq := rfl }
      after := EqClosure.refl commTarget }⟩

/-- Erasing the concrete event recovers its semantic communication step. -/
theorem rhoCommunicationEvidence_erases :
    (rho.toUnpositioned.toExtensionalGSLTAt Srt.pr).Step
      (parT commInput commOutput) commTarget :=
  (rho.toUnpositioned.stepEvidenceAt Srt.pr).erase rhoCommunicationEvidence

/-- The equations-only rung keeps rho's structural congruence but has no
communication rule. -/
def rhoStatic : UnpositionedPresentation sig :=
  { rho.toUnpositioned with rules := [] }

theorem rhoStatic_right_unit (a : Term sig [] Srt.pr) :
    EqClosure rhoStatic.eqs (parT a nilP) a :=
  par_right_unit a

theorem rhoStatic_has_no_step (source target : Term sig [] Srt.pr) :
    ¬ (rhoStatic.toExtensionalGSLTAt Srt.pr).Step source target :=
  UnpositionedPresentation.no_step_of_empty_rules rhoStatic rfl source target

/-- An equations-only presentation also has no proof-relevant event. -/
theorem rhoStatic_has_no_evidence (source target : Term sig [] Srt.pr) :
    ¬ Nonempty ((rhoStatic.stepEvidenceAt Srt.pr).Evidence source target) := by
  intro event
  apply rhoStatic_has_no_step source target
  exact ((rhoStatic.stepEvidenceAt Srt.pr).erases_iff source target).mp event

/-- Forgetting the position does not create a raw step from the null process. -/
theorem unpositioned_nil_does_not_step (u : Term sig [] Srt.pr) :
    ¬ rho.toUnpositioned.Step nilP u := by
  intro step
  obtain ⟨i, fires⟩ := (rho.step_iff_toUnpositioned).mpr step
  have onlyRule : i = ⟨0, by decide⟩ := Fin.eq_of_val_eq (by
    have bound : i.val < 1 := by simpa [rho] using i.isLt
    change i.val = 0
    omega)
  subst i
  exact nil_does_not_step_in_context u fires

/-! ### The separating conjunction

Closing the structural type at the interaction former under the equations is
what turns the positional split into a separating conjunction. -/

/-- `SepAnd A B` holds of a process that is equationally a parallel
composition of a part satisfying `A` and a part satisfying `B`. -/
def SepAnd (A B : Pred sig [] Srt.pr) : Pred sig [] Srt.pr :=
  fun t => ∃ a b, EqClosure rhoE t (parT a b) ∧ A a ∧ B b

/-- **And it is commutative** -- exactly what the positional split is not. -/
theorem sepAnd_comm {A B : Pred sig [] Srt.pr} {t : Term sig [] Srt.pr}
    (h : SepAnd A B t) : SepAnd B A t := by
  obtain ⟨a, b, he, hA, hB⟩ := h
  exact ⟨b, a, EqClosure.trans he (par_comm a b), hB, hA⟩

/-- The positional structural type refines into the separating one. -/
theorem sepAnd_of_structural {A B : Pred sig [] Srt.pr} {t : Term sig [] Srt.pr}
    (h : structural Op.par (.cons A (.cons B .nil)) t) : SepAnd A B t := by
  obtain ⟨args, ht, hsat⟩ := h
  revert ht hsat
  match args with
  | .cons a (.cons b .nil) =>
      intro ht hsat
      refine ⟨a, b, ?_, hsat.1, hsat.2.1⟩
      rw [ht]
      exact EqClosure.refl _

/-! ### The sort slots of this modality -/

/-- The channel slot of the communication modality: its one rely input. -/
def chanSlot : Slot comm := .rely Srt.nm Var.zero channel_is_rely

/-- And its output slot. -/
def outSlot : Slot comm := .out

/-- The two are distinct, so the modality generated at this position carries
the slots the construction says it should: one per rely input, one output. -/
theorem chanSlot_ne_outSlot : chanSlot ≠ outSlot := by
  intro h
  simp [chanSlot, outSlot] at h

/-- The payload gets no slot.  Only rely inputs do, and the payload is local --
which is why the number of slots is a fact about the chosen position and not
about the rule's variable count. -/
theorem payload_has_no_slot :
    ¬ comm.RelyParameter (Var.succ Var.zero : Var G Srt.pr) :=
  fun hr => comm.rely_not_local _ hr payload_is_local

/-! ### The worked example's position, at the continuation abstraction -/

/-- The hole of the worked example binds the received name and takes the two
ambient variables.  Its binding arity is what the source writes as the carrier
`[Nm -> Pr]`. -/
abbrev holeArity : MetaArity sig := ([Srt.nm, Srt.nm, Srt.pr], Srt.pr)

/-- The signature with that hole adjoined. -/
abbrev holeSig : Signature := withMetas sig [holeArity]

/-- The hole, applied to the bound name and the two ambient variables. -/
abbrev holeAt : Term holeSig ([Srt.nm] ++ G) Srt.pr :=
  Term.op (S := holeSig) (Sum.inr (MetaOp.mk (M := [holeArity]) 0))
    (.cons (.var .zero)
      (.cons (.var (.succ .zero)) (.cons (.var (.succ (.succ .zero))) .nil)))

/-- `out(n, p) | for(x <- n){ [-] }` -- the worked example's one-hole context. -/
def contCtxt : Term holeSig G Srt.pr :=
  Term.op (S := holeSig) (Sum.inl Op.par)
    (.cons (Term.op (S := holeSig) (Sum.inl Op.out)
        (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil)))
      (.cons (Term.op (S := holeSig) (Sum.inl Op.inp)
          (.cons (.var .zero) (.cons holeAt .nil)))
        .nil))

/-- The selected abstraction: unquote the received name. -/
def contRedex : Term sig holeArity.1 holeArity.2 :=
  Term.op (S := sig) Op.drp (.cons (.var .zero) .nil)

/-- The left-hand side it decomposes. -/
def contLhs : Term sig G Srt.pr :=
  Term.op (S := sig) (Γ := G) Op.par
    (.cons (Term.op (S := sig) (Γ := G) Op.out
        (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil)))
      (.cons (Term.op (S := sig) (Γ := G) Op.inp
          (.cons (.var .zero)
            (.cons (Term.op (S := sig) (Γ := [Srt.nm] ++ G) Op.drp
              (.cons (.var .zero) .nil)) .nil)))
        .nil))

/-- **The worked example's redex position**, taken at the continuation
abstraction rather than at a variable. -/
def continuationPosition : AbstractionPosition sig holeArity G Srt.pr contLhs where
  ctxt := contCtxt
  redex := contRedex
  plugs := rfl

/-- The channel is a rely parameter. -/
theorem chan_rely :
    continuationPosition.RelyParameter (Var.zero : Var G Srt.nm) := by
  simp only [AbstractionPosition.RelyParameter]
  decide

/-- And so is the emitted process -- recovering the source's `V = {n, p}`. -/
theorem payload_rely :
    continuationPosition.RelyParameter (Var.succ Var.zero : Var G Srt.pr) := by
  simp only [AbstractionPosition.RelyParameter]
  decide

/-- The three sort slots of the worked example: two rely inputs and one
output. -/
def slotN : continuationPosition.Slot := .rely Srt.nm Var.zero chan_rely
def slotP : continuationPosition.Slot := .rely Srt.pr (Var.succ Var.zero) payload_rely
def slotOut : continuationPosition.Slot := .out

theorem slotN_ne_out : slotN ≠ slotOut := by
  intro h; simp [slotN, slotOut] at h

theorem slotP_ne_out : slotP ≠ slotOut := by
  intro h; simp [slotP, slotOut] at h

theorem slotN_ne_slotP : slotN ≠ slotP := by
  intro h; simp [slotN, slotP] at h

/-! ### A language fragment of this calculus -/

/-- The name-free fragment: no quoting and no dropping, so no reflection. -/
abbrev nameFree : LanguageFragment sig := fun _ o =>
  match o with
  | Op.quo => False
  | Op.drp => False
  | _ => True

/-- A process built without reflection lies in the fragment. -/
theorem par_nils_nameFree :
    InFragment nameFree
      (Term.op (S := sig) (Γ := []) Op.par (.cons nilP (.cons nilP .nil))) := by
  refine InFragment.op (F := nameFree) Op.par trivial ?_
  refine InFragmentArgs.cons ?_ (InFragmentArgs.cons ?_ InFragmentArgs.nil)
  · exact InFragment.op (F := nameFree) Op.nil trivial InFragmentArgs.nil
  · exact InFragment.op (F := nameFree) Op.nil trivial InFragmentArgs.nil

/-- A process that unquotes does not: restricting the language really removes
constructions, and here it removes exactly reflection. -/
theorem dropChan_not_nameFree : ¬ InFragment nameFree dropChan := by
  intro h
  cases h with
  | op _ hf _ => exact hf

/-- And the fragment is a genuine restriction of the whole signature. -/
theorem nameFree_lt_full :
    (∀ s (o : Op s), nameFree s o → fullFragment sig s o)
      ∧ ¬ (∀ s (o : Op s), fullFragment sig s o → nameFree s o) := by
  refine ⟨fun _ _ _ => trivial, ?_⟩
  intro h
  exact h Srt.nm Op.quo trivial

/-! ### Matching on this signature -/

/-- Operators of this signature have decidable equality at each sort. -/
instance opDecEq : ∀ s : Srt, DecidableEq (Op s) := by
  intro s a b
  cases a <;> cases b <;>
    first
      | exact isTrue rfl
      | exact isFalse (by intro h; cases h)

/-- The output half of the communication pattern, with its two variables. -/
abbrev outPattern : Term sig G Srt.pr :=
  Term.op (S := sig) (Γ := G) Op.out
    (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))

/-- A closed output on the channel `@0` carrying the null process. -/
abbrev outTarget : Term sig [] Srt.pr :=
  Term.op (S := sig) (Γ := []) Op.out (.cons chan (.cons nilP .nil))

/-- The matcher finds the pattern in the target. -/
theorem outPattern_matches : (matchT emptyPSub outPattern outTarget).isSome = true := by
  simp [matchT, matchA, emptyPSub, updatePSub]

/-- Control: it refuses a target with a different head. -/
theorem outPattern_does_not_match_nil :
    (matchT emptyPSub outPattern nilP).isNone = true := by
  simp [matchT]

/-- And whatever it returns is right, by the general soundness theorem: any
closing substitution realising the result carries the pattern to the target. -/
theorem outPattern_match_sound (acc : PSub sig G)
    (h : matchT emptyPSub outPattern outTarget = some acc)
    (sigma : Sub sig G []) (he : PExtends sigma acc) :
    bind sigma outPattern = outTarget :=
  matchT_sound emptyPSub acc outPattern outTarget h sigma he

/-! ### The matcher firing the communication rule -/

/-- The closed source of the communication, written out. -/
abbrev commTargetExpl : Term sig [] Srt.pr :=
  Term.op (S := sig) (Γ := []) Op.par
    (.cons (Term.op (S := sig) (Γ := []) Op.out (.cons chan (.cons nilP .nil)))
      (.cons (Term.op (S := sig) (Γ := []) Op.inp
          (.cons chan
            (.cons (Term.op (S := sig) (Γ := [Srt.nm] ++ []) Op.drp
              (.cons (.var .zero) .nil)) .nil)))
        .nil))

/-- **The matcher fires the communication rule.**  Its left-hand side, with the
continuation supplied, matches the closed source -- including through the input
former's binding argument, which the first-order layer handles by comparing the
body against the target's body seen in the opened scope. -/
theorem commLhs_matches :
    (matchT emptyPSub contLhs commTargetExpl).isSome = true := by
  simp only [contLhs, matchT, matchA, emptyPSub, updatePSub, weakenInto, rename,
    renameArgs]
  rfl

/-- Control: it does not fire on the null process. -/
theorem commLhs_does_not_match_nil :
    (matchT emptyPSub contLhs nilP).isNone = true := by
  simp [contLhs, matchT]

/-! ### Carrying a position along an instantiation -/

/-- A unary metavariable over processes. -/
abbrev discardMetas : List (MetaArity sig) := [([Srt.pr], Srt.pr)]

/-- A one-hole context whose hole is used only as that metavariable's
argument. -/
abbrev metaHoleCtxt : Term (withMetas sig discardMetas) [Srt.pr] Srt.pr :=
  Term.op (S := withMetas sig discardMetas) (Sum.inr (MetaOp.mk (M := discardMetas) 0))
    (.cons (.var .zero) .nil)

/-- It uses its hole exactly once, so it is an admissible context. -/
theorem metaHoleCtxt_linear : holeCount metaHoleCtxt = 1 := rfl

/-- A continuation that discards what it is given. -/
def discardBody : (i : Fin discardMetas.length) →
    Term (withMetas sig []) (discardMetas.get i).1 (discardMetas.get i).2
  | ⟨0, _⟩ => Term.op (S := withMetas sig []) (Sum.inl Op.nil) .nil

/-- Instantiating with it erases the hole. -/
theorem instInto_discard_erases :
    holeCount (instInto discardBody metaHoleCtxt) = 0 := rfl

/-- **Instantiation does not preserve a redex position.**  A supplied body that
discards its argument erases the hole, so the transported context no longer
uses it.  The action on positions is therefore partial: carrying a position
along an instantiation needs the supplied bodies to actually use the argument
that carries the hole, and that condition is not automatic. -/
theorem instInto_destroys_position :
    holeCount metaHoleCtxt = 1 ∧ holeCount (instInto discardBody metaHoleCtxt) ≠ 1 := by
  refine ⟨metaHoleCtxt_linear, ?_⟩
  rw [instInto_discard_erases]
  exact Nat.zero_ne_one

end RhoSchema

end Mettapedia.OSLF.Binding
