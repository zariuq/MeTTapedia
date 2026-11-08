import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersPrincipal
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LambdaComparison

/-!
# Controls for pattern equations under binders

The constants are `f` and `g`, the ambient context `[f, g]`.
- **η:** `(= (f (λx. $M x)) (λz. $M z))` at `(f (λy. g y))` gives exactly `λz. g z`, which
  η-contracts to `g`; it is not syntactically `g`. The same holds on the step, where the answer is
  principal.
- **Two branches:** with `(= (f (λx. ($A x) ($B x))) (λz. $B z))` beside it, the call has exactly
  the two answers `λz. g z` and `λz. z`, and the step has exactly two firings with those readings.
- **No capture:** `(= (f (λx. $N)) $N)`, where `$N` does not list `x`, refuses `(f (λy. y))`: no
  source answer, no admitted firing, and the actual worklist refutes. It answers `(f (λy. g))` by `g`.
- **Two-way:** `(= g $Y)` leaves an unknown in the store, which reads every term. The η equation
  then unifies that unknown with its binder pattern and binds it (`unknown_after_first`,
  `two_way_on_step`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open LambdaContextualRung (sig Srt)

/-! ## The λ signature as an instance -/

scoped instance : DecidableEq sig.Srt := inferInstanceAs (DecidableEq Srt)
scoped instance (sort : sig.Srt) : DecidableEq (sig.Op sort) := by
  cases sort
  intro first second
  cases first <;> cases second
  · exact isTrue rfl
  · exact isFalse (by intro same; cases same)
  · exact isFalse (by intro same; cases same)
  · exact isTrue rfl

/-- The identity `λx. x` is a closed term of the only sort. -/
instance : ClosedTerms sig := ⟨fun | .term => LambdaContextualRung.lamT (.var .zero)⟩

/-- Holes of sort `term`, with the given parameter contexts. -/
abbrev holeArity {H : Type} (params : H → Ctx sig) : H → MetaArity sig := fun hole => (params hole, .term)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open LambdaContextualRung (sig Srt appT lamT)
open LambdaComparison (app lam app_inj lam_inj)
open ContextualPatternFragment (Pattern)

/-- The constants `f` (position 0) and `g` (position 1). -/
abbrev Consts : Ctx sig := [.term, .term]

def fC : Term sig Consts .term := .var .zero
def gC : Term sig Consts .term := .var (.succ .zero)

/-- `λz. t z`. -/
def etaExpand {Δ : Ctx sig} (t : Term sig Δ .term) : Term sig Δ .term := lamT (appT (weaken t) (.var .zero))

/-- η-contraction at the root. -/
inductive EtaContracts {Δ : Ctx sig} : Term sig Δ .term → Term sig Δ .term → Prop
  | eta (t : Term sig Δ .term) : EtaContracts (etaExpand t) t

theorem etaContracts_iff {Δ : Ctx sig} (source target : Term sig Δ .term) :
    EtaContracts source target ↔ source = etaExpand target := by
  constructor
  · rintro ⟨_⟩
    rfl
  · rintro rfl
    exact .eta target

theorem lamT_inj {Δ : Ctx sig} {first second : Term sig (.term :: Δ) .term} (same : lamT first = lamT second) :
    first = second :=
  (Args.cons.inj (eq_of_heq (Term.op.inj same).2)).1

theorem appT_inj {Δ : Ctx sig} {first second third fourth : Term sig Δ .term}
    (same : appT first second = appT third fourth) : first = third ∧ second = fourth := by
  have fields := Args.cons.inj (eq_of_heq (Term.op.inj same).2)
  exact ⟨fields.1, (Args.cons.inj fields.2).1⟩

/-- Weakening never produces the newly bound variable: the reason a hole that does not list a
binder cannot capture it. -/
theorem weaken_ne_bound {S : Signature} {Δ : Ctx S} {s : S.Srt} (t : Term S Δ s) :
    weaken (t := s) t ≠ .var .zero := by
  cases t with
  | var v => intro same; cases same
  | op o arguments => intro same; cases same

/-! ## η -/

abbrev unary : Unit → Ctx sig := fun _ => .term :: Consts

def lhsEta : Term (signature sig (holeArity unary)) Consts .term :=
  app _ (.var .zero) (lam _ (generator _ ()))

def rhsEta : Term (signature sig (holeArity unary)) Consts .term := lam _ (generator _ ())

/-- `(= (f (λx. $M x)) (λz. $M z))`. -/
def etaEquation : Equation sig Consts .term := ⟨Unit, inferInstance, holeArity unary, lhsEta, rhsEta⟩

/-- `(f (λy. g y))`. -/
def callEta : Term sig Consts .term := appT fC (lamT (appT (.var (.succ (.succ .zero))) (.var .zero)))

theorem instantiate_lhsEta {W : Type} {target : W → MetaArity sig} (change : Assignment (holeArity unary) target) :
    instantiate change lhsEta = app target (.var .zero) (lam target (change ())) := by
  change app target (.var .zero) (lam target (instantiate change (generator _ ()))) = _
  rw [instantiate_generator]

theorem instantiate_rhsEta {W : Type} {target : W → MetaArity sig} (change : Assignment (holeArity unary) target) :
    instantiate change rhsEta = lam target (change ()) := by
  change lam target (instantiate change (generator _ ())) = _
  rw [instantiate_generator]

theorem lhsEta_pattern : Pattern sig etaEquation.arity etaEquation.lhs :=
  .rigid (S := sig) LambdaContextualRung.Op.app _
    (.cons _ _ (.object _) (.cons _ _ (.rigid (S := sig) LambdaContextualRung.Op.lam _
      (.cons _ _ (ContextualPatternFragment.generator_pattern _) .nil)) .nil))

/-- The branch of the η equation at `(f (λy. g y))` has exactly one answer, `λz. g z`. -/
theorem eta_answers (answer : Term sig Consts .term) :
    Answers etaEquation callEta answer ↔ answer = etaExpand gC := by
  constructor
  · rintro ⟨θ, matched, answered⟩
    change instantiate (etaEquation.assign θ (ground sig)) lhsEta = Rigid.includeTerm (ground sig) callEta at matched
    change instantiate (etaEquation.assign θ (ground sig)) rhsEta = Rigid.includeTerm (ground sig) answer at answered
    rw [instantiate_lhsEta] at matched
    rw [instantiate_rhsEta] at answered
    have body := lam_inj (app_inj matched).2
    have image : θ () = appT (.var (.succ (.succ .zero))) (.var .zero) := Rigid.include_injective _ _ _ body
    have result : lamT (θ ()) = answer := Rigid.include_injective _ _ _ answered
    rw [← result, image]
    rfl
  · rintro rfl
    refine ⟨fun _ => appT (.var (.succ (.succ .zero))) (.var .zero), ?_, ?_⟩
    · change instantiate (etaEquation.assign _ (ground sig)) lhsEta = Rigid.includeTerm (ground sig) callEta
      rw [instantiate_lhsEta]
      rfl
    · change instantiate (etaEquation.assign _ (ground sig)) rhsEta = Rigid.includeTerm (ground sig) (etaExpand gC)
      rw [instantiate_rhsEta]
      rfl

/-- The answer η-contracts to `g`. -/
theorem eta_contracts_to_g : EtaContracts (etaExpand gC) gC := .eta gC

/-- The answer is `g` only up to η. -/
theorem eta_answer_is_not_g : etaExpand gC ≠ gC := by
  intro same
  cases same

/-- A negative example of η: `λz. z z` contracts to nothing, since the head would have to be the
bound variable. -/
theorem self_application_not_eta {t : Term sig Consts .term} :
    ¬ EtaContracts (lamT (appT (.var .zero) (.var .zero))) t := by
  intro contracts
  have shape := (etaContracts_iff _ _).mp contracts
  exact weaken_ne_bound t (appT_inj (lamT_inj shape)).1.symm

def etaProgram : Unit → Equation sig Consts .term := fun _ => etaEquation

/-- On the step: the firing is admitted, its result reads exactly `λz. g z`, and the actual
worklist computes that answer as a principal one. -/
theorem eta_on_step :
    ∃ valid : Admitted etaProgram (initial callEta) (),
      (∀ answer, Reads etaProgram (destination etaProgram (initial callEta) () valid) answer ↔
        answer = etaExpand gC) ∧
      ∃ (fuel : Nat) (update : ContextualFrameUpdate.Update (firingProblem (initial (program := etaProgram) callEta) ())),
        (letI := (destination etaProgram (initial callEta) () valid).1.equality;
          ContextualFrameWorklist.run fuel (active etaProgram (initial (program := etaProgram) callEta).1.declarations)
            (firingProblem (initial (program := etaProgram) callEta) ())) = .residual update ∧
        update.remaining = [] := by
  have valid : Admitted etaProgram (initial callEta) () :=
    (valid_iff (initial callEta) callEta (initial_determines callEta) ()).mpr
      ⟨_, ((eta_answers (etaExpand gC)).mpr rfl).choose_spec.1⟩
  refine ⟨valid, fun answer => (reads_iff (initial callEta) callEta (initial_determines callEta) () valid answer).trans
    (eta_answers answer), ?_⟩
  obtain ⟨fuel, update, computed, empty, _⟩ := principal_firing (initial callEta) () valid
    (initial_pattern callEta) lhsEta_pattern
  exact ⟨fuel, update, computed, empty⟩

/-! ## Two equations with binder patterns -/

abbrev split : Bool → Ctx sig := fun _ => .term :: Consts

def lhsSplit : Term (signature sig (holeArity split)) Consts .term :=
  app _ (.var .zero) (lam _ (app _ (generator _ true) (generator _ false)))

def rhsSplit : Term (signature sig (holeArity split)) Consts .term := lam _ (generator _ false)

/-- `(= (f (λx. ($A x) ($B x))) (λz. $B z))`. -/
def splitEquation : Equation sig Consts .term := ⟨Bool, inferInstance, holeArity split, lhsSplit, rhsSplit⟩

theorem instantiate_lhsSplit {W : Type} {target : W → MetaArity sig} (change : Assignment (holeArity split) target) :
    instantiate change lhsSplit = app target (.var .zero) (lam target (app target (change true) (change false))) := by
  change app target (.var .zero) (lam target (app target (instantiate change (generator _ true))
    (instantiate change (generator _ false)))) = _
  rw [instantiate_generator, instantiate_generator]

theorem instantiate_rhsSplit {W : Type} {target : W → MetaArity sig} (change : Assignment (holeArity split) target) :
    instantiate change rhsSplit = lam target (change false) := by
  change lam target (instantiate change (generator _ false)) = _
  rw [instantiate_generator]

theorem split_answers (answer : Term sig Consts .term) :
    Answers splitEquation callEta answer ↔ answer = lamT (.var .zero) := by
  constructor
  · rintro ⟨θ, matched, answered⟩
    change instantiate (splitEquation.assign θ (ground sig)) lhsSplit = Rigid.includeTerm (ground sig) callEta at matched
    change instantiate (splitEquation.assign θ (ground sig)) rhsSplit = Rigid.includeTerm (ground sig) answer at answered
    rw [instantiate_lhsSplit] at matched
    rw [instantiate_rhsSplit] at answered
    have body := app_inj (lam_inj (app_inj matched).2)
    have image : θ false = .var .zero := Rigid.include_injective _ _ _ body.2
    have result : lamT (θ false) = answer := Rigid.include_injective _ _ _ answered
    rw [← result, image]
  · rintro rfl
    refine ⟨fun (hole : Bool) => cond hole (.var (.succ (.succ .zero))) (.var .zero), ?_, ?_⟩
    · change instantiate (splitEquation.assign _ (ground sig)) lhsSplit = Rigid.includeTerm (ground sig) callEta
      rw [instantiate_lhsSplit]
      rfl
    · change instantiate (splitEquation.assign _ (ground sig)) rhsSplit = Rigid.includeTerm (ground sig) (lamT (.var .zero))
      rw [instantiate_rhsSplit]
      rfl

def twoProgram : Bool → Equation sig Consts .term
  | true => etaEquation
  | false => splitEquation

/-- Both equations match, giving exactly two answers. -/
theorem two_answers (answer : Term sig Consts .term) :
    Rewrites twoProgram callEta answer ↔ answer = etaExpand gC ∨ answer = lamT (.var .zero) := by
  constructor
  · rintro ⟨index, answered⟩
    cases index with
    | true => exact .inl ((eta_answers answer).mp answered)
    | false => exact .inr ((split_answers answer).mp answered)
  · rintro (same | same)
    · exact ⟨true, (eta_answers answer).mpr same⟩
    · exact ⟨false, (split_answers answer).mpr same⟩

theorem two_answers_distinct : etaExpand gC ≠ lamT (.var .zero) := by
  intro same
  cases same

/-- On the step: both firings are admitted, and the firings from the initial state read exactly
the two answers. -/
theorem two_answers_on_step :
    Admitted twoProgram (initial callEta) true ∧ Admitted twoProgram (initial callEta) false ∧
      ∀ answer, (∃ after, Transition twoProgram (initial callEta) after ∧ Reads twoProgram after answer) ↔
        answer = etaExpand gC ∨ answer = lamT (.var .zero) := by
  have determined := initial_determines (program := twoProgram) callEta
  refine ⟨(valid_iff _ _ determined true).mpr ⟨_, ((eta_answers (etaExpand gC)).mpr rfl).choose_spec.1⟩,
    (valid_iff _ _ determined false).mpr ⟨_, ((split_answers (lamT (.var .zero))).mpr rfl).choose_spec.1⟩,
    fun answer => ⟨?_, ?_⟩⟩
  · rintro ⟨after, ⟨index, valid, rfl⟩, reads⟩
    exact (two_answers answer).mp ⟨index, (reads_iff _ _ determined index valid answer).mp reads⟩
  · intro answered
    obtain ⟨index, branch⟩ := (two_answers answer).mpr answered
    obtain ⟨θ, matched, read⟩ := branch
    have valid := (valid_iff _ _ determined index).mpr ⟨θ, matched⟩
    exact ⟨_, ⟨index, valid, rfl⟩, (reads_iff _ _ determined index valid answer).mpr ⟨θ, matched, read⟩⟩

/-! ## No capture -/

abbrev outer : Unit → Ctx sig := fun _ => Consts

def lhsCapture : Term (signature sig (holeArity outer)) Consts .term :=
  app _ (.var .zero) (lam _ (weaken (generator _ ())))

/-- `(= (f (λx. $N)) $N)`: the hole `$N` lists only the constants, not `x`. -/
def captureEquation : Equation sig Consts .term := ⟨Unit, inferInstance, holeArity outer, lhsCapture, generator _ ()⟩

/-- `(f (λy. y))`: a solution would have to capture `y`. -/
def captureCall : Term sig Consts .term := appT fC (lamT (.var .zero))

/-- `(f (λy. g))`. -/
def constantCall : Term sig Consts .term := appT fC (lamT (.var (.succ (.succ .zero))))

theorem instantiate_lhsCapture {W : Type} {target : W → MetaArity sig}
    (change : Assignment (holeArity outer) target) :
    instantiate change lhsCapture = app target (.var .zero) (lam target (weaken (change ()))) := by
  change app target (.var .zero) (lam target (instantiate change (weaken (generator _ ())))) = _
  rw [weaken, ContextualFamily.instantiate_rename, instantiate_generator]
  rfl

theorem lhsCapture_pattern : Pattern sig captureEquation.arity captureEquation.lhs :=
  .rigid (S := sig) LambdaContextualRung.Op.app _
    (.cons _ _ (.object _) (.cons _ _ (.rigid (S := sig) LambdaContextualRung.Op.lam _
      (.cons _ _ (ContextualPatternFragment.rename_preserves _ (ContextualPatternFragment.generator_pattern _) _
        (fun _ _ _ same => Var.succ.inj same)) .nil)) .nil))

/-- The capturing call has no solution. -/
theorem capture_unmatched (θ : captureEquation.Ground) : ¬ Matches captureEquation captureCall θ := by
  intro matched
  change instantiate (captureEquation.assign θ (ground sig)) lhsCapture = Rigid.includeTerm (ground sig) captureCall at matched
  rw [instantiate_lhsCapture] at matched
  exact weaken_ne_bound _ (lam_inj (app_inj matched).2)

theorem capture_refused (answer : Term sig Consts .term) : ¬ Answers captureEquation captureCall answer :=
  fun ⟨θ, matched, _⟩ => capture_unmatched θ matched

/-- The actual worklist refutes the capturing problem. -/
theorem capture_refuted_by_solver :
    ∃ fuel proof, ContextualFrameWorklist.run fuel captureEquation.arity (problem captureEquation captureCall) =
      .refuted proof :=
  refuted_of_no_match captureEquation lhsCapture_pattern captureCall capture_unmatched

def captureProgram : Unit → Equation sig Consts .term := fun _ => captureEquation

/-- On the step the capturing firing is refused. -/
theorem capture_refused_on_step : ¬ Admitted captureProgram (initial captureCall) () := by
  intro valid
  obtain ⟨θ, matched⟩ := (valid_iff _ _ (initial_determines captureCall) ()).mp valid
  exact capture_unmatched θ matched

/-- The contrast: a λ that does not use its bound variable is matched, with answer `g`. -/
theorem constant_answers : Answers captureEquation constantCall gC := by
  refine ⟨fun _ => gC, ?_, rfl⟩
  change instantiate (captureEquation.assign _ (ground sig)) lhsCapture = Rigid.includeTerm (ground sig) constantCall
  rw [instantiate_lhsCapture]
  rfl

/-! ## Two-way: the caller's unknown is bound by a binder pattern -/

/-- `(= g $Y)`: the right-hand side's hole occurs nowhere on the left, so the answer is unknown. -/
def unknownEquation : Equation sig Consts .term :=
  ⟨Unit, inferInstance, holeArity outer, .var (.succ .zero), generator _ ()⟩

theorem unknown_answers (answer : Term sig Consts .term) : Answers unknownEquation gC answer :=
  ⟨fun _ => answer, rfl, instantiate_generator _ ()⟩

def twoWayProgram : Bool → Equation sig Consts .term
  | true => unknownEquation
  | false => etaEquation

/-- After the first firing the store keeps an unknown: the call reads as `(f (λy. g y))` and as `f`. -/
theorem unknown_after_first :
    ∃ valid : Admitted twoWayProgram (initial gC) true,
      Reads twoWayProgram (destination twoWayProgram (initial gC) true valid) callEta ∧
        Reads twoWayProgram (destination twoWayProgram (initial gC) true valid) fC ∧ callEta ≠ fC := by
  have determined := initial_determines (program := twoWayProgram) gC
  have valid : Admitted twoWayProgram (initial gC) true :=
    (valid_iff _ _ determined true).mpr ⟨fun _ => fC, rfl⟩
  refine ⟨valid, (reads_iff _ _ determined true valid _).mpr (unknown_answers _),
    (reads_iff _ _ determined true valid _).mpr (unknown_answers _), ?_⟩
  intro same
  cases same

/-- **Two-way on the step.** The second firing unifies the stored unknown with the binder pattern
`(f (λx. $M x))`, binding the caller's hole; the run reads `λz. g z`. -/
theorem two_way_on_step :
    ∃ after, Relation.ReflTransGen (Transition twoWayProgram) (initial gC) after ∧
      Reads twoWayProgram after (etaExpand gC) :=
  (execution_iff _ _).mp ((Relation.ReflTransGen.single ⟨true, unknown_answers callEta⟩).tail
    ⟨false, (eta_answers _).mpr rfl⟩)

theorem twoWay_patterns (rule : Bool) :
    Pattern sig (twoWayProgram rule).arity (twoWayProgram rule).lhs ∧
      Pattern sig (twoWayProgram rule).arity (twoWayProgram rule).rhs := by
  cases rule with
  | true => exact ⟨.object _, ContextualPatternFragment.generator_pattern _⟩
  | false => exact ⟨lhsEta_pattern, .rigid (S := sig) LambdaContextualRung.Op.lam _
      (.cons _ _ (ContextualPatternFragment.generator_pattern _) .nil)⟩

/-- **Principal at every firing of every run**, unknowns included: both equations are Miller patterns
on both sides, so every reachable store stays in the fragment. -/
theorem two_way_principal {state : State twoWayProgram}
    (path : Relation.ReflTransGen (Transition twoWayProgram) (initial gC) state) (rule : Bool)
    (valid : Admitted twoWayProgram state rule) :
    ∃ (fuel : Nat) (update : ContextualFrameUpdate.Update (firingProblem state rule)),
      (letI := (destination twoWayProgram state rule valid).1.equality;
        ContextualFrameWorklist.run fuel (active twoWayProgram state.1.declarations) (firingProblem state rule)) =
          .residual update ∧
        update.remaining = [] := by
  obtain ⟨fuel, update, computed, empty, _⟩ := principal_firing state rule valid
    (reachable_pattern twoWay_patterns path) (twoWay_patterns rule).1
  exact ⟨fuel, update, computed, empty⟩

#print axioms unknown_answers
#print axioms unknown_after_first
#print axioms two_way_on_step
#print axioms two_way_principal
#print axioms eta_answers
#print axioms eta_contracts_to_g
#print axioms eta_answer_is_not_g
#print axioms self_application_not_eta
#print axioms eta_on_step
#print axioms split_answers
#print axioms two_answers
#print axioms two_answers_distinct
#print axioms two_answers_on_step
#print axioms capture_unmatched
#print axioms capture_refused
#print axioms capture_refuted_by_solver
#print axioms capture_refused_on_step
#print axioms constant_answers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.Controls
