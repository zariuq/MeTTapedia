import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes
import Mettapedia.GSLT.Core.OperationalPathFibration

/-!
# Channel roles derived for the name-passing compiler

Reference channels perform unary lookup and transport a call/result name.
Call channels perform binary invocation and transport a reference name followed
by a call/result name. Receiver roles follow the actual simultaneous binder
order of the intrinsic syntax. Application allocates a private call channel;
definition allocates a private reference channel.

The judgment concerns the existing shared process syntax. It supplies a
compiler-image discipline, rather than a new calculus or a restriction
silently imposed on arbitrary untyped target processes. Distinct reference
names may still be identified by a role-preserving environment, so roles alone
do not establish faithful name transport or arbitrary-schedule reflection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingChannelRoles

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda

inductive Role where
  | reference
  | call
  deriving DecidableEq, Repr

abbrev Roles (Γ : Ctx sig) := Var Γ Srt.nm → Role

/-- Assign a role to the new name and retain every ambient name's role. -/
def extendRole {Γ : Ctx sig} (fresh : Role) (roles : Roles Γ) : Roles (.nm :: Γ)
  | .zero => fresh
  | .succ old => roles old

/-- The first binary field is the reference at position zero. The second is
the call/result name at position one. -/
def pairRoles {Γ : Ctx sig} (roles : Roles Γ) : Roles (.nm :: .nm :: Γ) :=
  extendRole .reference (extendRole .call roles)

inductive Typed : {Γ : Ctx sig} → Roles Γ → Proc Γ → Prop where
  | nil {Γ} (roles : Roles Γ) : Typed roles nil
  | par {Γ} {roles : Roles Γ} {first second : Proc Γ} :
      Typed roles first → Typed roles second → Typed roles (par first second)
  | out1 {Γ} {roles : Roles Γ} (channel datum : Var Γ .nm) :
      roles channel = .reference → roles datum = .call →
        Typed roles (out1 (.var channel) (.var datum))
  | inp1 {Γ} {roles : Roles Γ} (channel : Var Γ .nm) {body : Proc (.nm :: Γ)} :
      roles channel = .reference → Typed (extendRole .call roles) body →
        Typed roles (inp1 (.var channel) body)
  | out2 {Γ} {roles : Roles Γ} (channel first second : Var Γ .nm) :
      roles channel = .call → roles first = .reference → roles second = .call →
        Typed roles (out2 (.var channel) (.var first) (.var second))
  | inp2 {Γ} {roles : Roles Γ} (channel : Var Γ .nm) {body : Proc (.nm :: .nm :: Γ)} :
      roles channel = .call → Typed (pairRoles roles) body →
        Typed roles (inp2 (.var channel) body)
  | nu {Γ} {roles : Roles Γ} {body : Proc (.nm :: Γ)} (fresh : Role) :
      Typed (extendRole fresh roles) body → Typed roles (nu body)
  | rep {Γ} {roles : Roles Γ} {body : Proc Γ} :
      Typed roles body → Typed roles (rep body)

/-- The compiler's source environment supplies reference names. It may
identify two references, but it may not identify one with a call channel. -/
def ReferenceEnvironment {Γ Δ : Ctx sig} (roles : Roles Δ) (environment : Ren sig Γ Δ) : Prop :=
  ∀ name : Var Γ .nm, roles (environment _ name) = .reference

theorem push_reference_environment {Γ Δ : Ctx sig} (roles : Roles Δ)
    (environment : Ren sig Γ Δ) (reference : ReferenceEnvironment roles environment)
    (fresh : Role) : ReferenceEnvironment (extendRole fresh roles) (push environment) :=
  reference

theorem bound_reference_environment {Γ Δ : Ctx sig} (roles : Roles Δ)
    (environment : Ren sig Γ Δ) (reference : ReferenceEnvironment roles environment) :
    ReferenceEnvironment (extendRole .reference roles) (liftRen environment [.nm]) := by
  intro name
  cases name with
  | zero => rfl
  | succ old => exact reference old

theorem call_reference_environment {Γ Δ : Ctx sig} (roles : Roles Δ)
    (environment : Ren sig Γ Δ) (reference : ReferenceEnvironment roles environment) :
    ReferenceEnvironment (pairRoles roles) (callEnv environment) := by
  intro name
  cases name with
  | zero => rfl
  | succ old => exact reference old

/-- Every actual compiler clause satisfies the reference/call discipline.
No source term typing or result computed afterward is supplied as a premise. -/
theorem compile_typed {Γ Δ : Ctx sig} (term : Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) (roles : Roles Δ)
    (reference : ReferenceEnvironment roles environment) (call : roles result = .call) :
    Typed roles (compile term environment result) := by
  induction term generalizing Δ with
  | var name => exact .out1 _ _ (reference name) call
  | lam body ih =>
      exact .inp2 _ call (ih (callEnv environment) (.succ .zero) (pairRoles roles)
        (call_reference_environment roles environment reference) rfl)
  | app function argument ih =>
      apply Typed.nu .call
      apply Typed.par
      · exact ih (push environment) .zero (extendRole .call roles)
          (push_reference_environment roles environment reference .call) rfl
      · exact .out2 _ _ _ rfl (reference argument) call
  | defn value body valueIH bodyIH =>
      apply Typed.nu .reference
      apply Typed.par
      · exact bodyIH (liftRen environment [.nm]) (.succ result) (extendRole .reference roles)
          (bound_reference_environment roles environment reference) call
      · apply Typed.rep
        apply Typed.inp1 _ rfl
        exact valueIH (push (push environment)) .zero
          (extendRole .call (extendRole .reference roles))
          (push_reference_environment _ _
            (push_reference_environment roles environment reference .reference) .call) rfl
  | carrier name value body valueIH bodyIH =>
      apply Typed.par
      · exact bodyIH environment result roles reference call
      · apply Typed.inp1 _ (reference name)
        exact valueIH (push environment) .zero (extendRole .call roles)
          (push_reference_environment roles environment reference .call) rfl

/-- The supplied call/result name cannot alias any source reference image. -/
theorem result_not_reference_image {Γ Δ : Ctx sig} (roles : Roles Δ)
    (environment : Ren sig Γ Δ) (reference : ReferenceEnvironment roles environment)
    (result : Var Δ .nm) (call : roles result = .call) (name : Var Γ .nm) :
    result ≠ environment _ name := by
  intro equal
  rw [equal, reference name] at call
  cases call

def referenceRoles (Γ : Ctx sig) : Roles Γ := fun _ => .reference

def canonicalRoles (Γ : Ctx sig) : Roles (.nm :: Γ) :=
  extendRole .call (referenceRoles Γ)

/-- A fresh return name realizes the image discipline for every source term,
including open terms with arbitrarily many source references. -/
theorem fresh_result_compile_typed {Γ : Ctx sig} (term : Expr Γ) :
    Typed (canonicalRoles Γ) (compile term (fun _ name => .succ name) .zero) :=
  compile_typed term _ _ _ (fun _ => rfl) rfl

/-- Role-preserving ambient name maps fix newly bound names' roles. -/
theorem extend_roles_preserved {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (source : Roles Γ) (target : Roles Δ)
    (preserved : ∀ name, target (environment _ name) = source name) (fresh : Role) :
    ∀ name : Var (Srt.nm :: Γ) Srt.nm,
      extendRole fresh target (liftRen environment [.nm] _ name) = extendRole fresh source name := by
  intro name
  cases name with
  | zero => rfl
  | succ old => exact preserved old

/-- Name reindexing preserves the discipline when it preserves roles,
including the two differently typed binary receiver binders. -/
theorem Typed.rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    {source : Roles Γ} {target : Roles Δ} {process : Proc Γ}
    (typed : Typed source process) (preserved : ∀ name, target (environment _ name) = source name) :
    Typed target (rename environment process) := by
  induction typed generalizing Δ with
  | nil roles => exact .nil _
  | par _ _ firstIH secondIH => exact .par (firstIH environment preserved) (secondIH environment preserved)
  | out1 channel datum reference call =>
      exact .out1 _ _ ((preserved channel).trans reference) ((preserved datum).trans call)
  | inp1 channel reference _ ih =>
      exact .inp1 _ ((preserved channel).trans reference)
        (ih (liftRen environment [.nm]) (extend_roles_preserved _ _ _ preserved .call))
  | out2 channel first second call reference result =>
      exact .out2 _ _ _ ((preserved channel).trans call)
        ((preserved first).trans reference) ((preserved second).trans result)
  | inp2 channel call _ ih =>
      apply Typed.inp2 _ ((preserved channel).trans call)
      apply ih (liftRen environment [.nm, .nm])
      intro name
      cases name with
      | zero => rfl
      | succ name => cases name with
          | zero => rfl
          | succ old => exact preserved old
  | nu fresh _ ih =>
      exact .nu fresh (ih (liftRen environment [.nm])
        (extend_roles_preserved _ _ _ preserved fresh))
  | rep _ ih => exact .rep (ih environment preserved)

/-- Unary receive opens a call/result name, preserving every ambient role. -/
theorem Typed.openUnary {Γ : Ctx sig} {roles : Roles Γ} {body : Proc (.nm :: Γ)}
    (typed : Typed (extendRole .call roles) body) (datum : Var Γ .nm)
    (call : roles datum = .call) : Typed roles (inst body (.var datum)) := by
  unfold inst
  have environment : extend (Term.var datum) =
      (fun sort name => Term.var (nameRen datum sort name)) := by
    funext sort name
    cases name <;> rfl
  rw [environment, bind_var_eq_rename]
  apply typed.rename (nameRen datum)
  intro name
  cases name with
  | zero => exact call
  | succ old => rfl

/-- The simultaneous binary opening preserves the actual reference/call
order, and does not change the roles of enclosing names. -/
theorem Typed.openBinary {Γ : Ctx sig} {roles : Roles Γ} {body : Proc (.nm :: .nm :: Γ)}
    (typed : Typed (pairRoles roles) body) (first second : Var Γ .nm)
    (reference : roles first = .reference) (call : roles second = .call) :
    Typed roles (openPair body (.var first) (.var second)) := by
  rw [openPair_variables]
  apply typed.rename (pairRen first second)
  intro name
  cases name with
  | zero => exact reference
  | succ name => cases name with
      | zero => exact call
      | succ old => rfl

/-- Role typing is preserved by the supplied actual raw communication and
parallel/restriction descent. Structural-equation closure and the lowered
handshake protocol are separate contracts. -/
theorem Typed.raw_step {Γ : Ctx sig} {roles : Roles Γ} {source target : Proc Γ}
    (typed : Typed roles source) (step : Step source target) : Typed roles target := by
  induction step with
  | comm1 channel datum body =>
      cases typed with
      | par output input =>
          cases output with
          | out1 channel datum reference call =>
              cases input with
              | inp1 _ _ bodyTyped => exact bodyTyped.openUnary datum call
  | comm2 channel first second body =>
      cases typed with
      | par output input =>
          cases output with
          | out2 channel first second call reference result =>
              cases input with
              | inp2 _ _ bodyTyped => exact bodyTyped.openBinary first second reference result
  | parL frame _ ih =>
      cases typed with
      | par sourceTyped frameTyped => exact .par (ih sourceTyped) frameTyped
  | parR frame _ ih =>
      cases typed with
      | par frameTyped sourceTyped => exact .par frameTyped (ih sourceTyped)
  | nu _ ih =>
      cases typed with
      | nu fresh bodyTyped => exact .nu fresh (ih bodyTyped)

/-- Role-preserving reindexing also reflects the judgment. This is a syntax
invariant, and does not reflect executions introduced by merging names. -/
theorem Typed.reflectRename : ∀ {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (source : Roles Γ) (target : Roles Δ)
    (_preserved : ∀ name, target (environment _ name) = source name) (process : Proc Γ),
    Typed target (Mettapedia.OSLF.Binding.rename environment process) → Typed source process
  | _, _, _, _, _, _, .var _, typed => by cases typed
  | _, _, _, source, _, _, .op .nil .nil, _ => .nil source
  | _, _, environment, source, target, preserved, .op .par (.cons first (.cons second .nil)), typed => by
      cases typed with
      | par firstTyped secondTyped =>
          exact .par (Typed.reflectRename environment source target preserved first firstTyped)
            (Typed.reflectRename environment source target preserved second secondTyped)
  | _, _, environment, source, target, preserved, .op .inp1 (.cons channel (.cons body .nil)), typed => by
      cases channel with
      | op op args => cases op
      | var channel =>
          cases typed with
          | inp1 _ reference bodyTyped =>
              exact .inp1 _ ((preserved channel).symm.trans reference)
                (Typed.reflectRename (liftRen environment [.nm])
                  (extendRole .call source) (extendRole .call target)
                  (extend_roles_preserved _ _ _ preserved .call) body bodyTyped)
  | _, _, environment, source, target, preserved, .op .inp2 (.cons channel (.cons body .nil)), typed => by
      cases channel with
      | op op args => cases op
      | var channel =>
          cases typed with
          | inp2 _ call bodyTyped =>
              apply Typed.inp2 _ ((preserved channel).symm.trans call)
              apply Typed.reflectRename (liftRen environment [.nm, .nm])
                (pairRoles source) (pairRoles target) _ body bodyTyped
              intro name
              cases name with
              | zero => rfl
              | succ name => cases name with
                  | zero => rfl
                  | succ old => exact preserved old
  | _, _, environment, source, target, preserved, .op .out1 (.cons channel (.cons datum .nil)), typed => by
      cases channel with
      | op op args => cases op
      | var channel =>
          cases datum with
          | op op args => cases op
          | var datum =>
              cases typed with
              | out1 _ _ reference call =>
                  exact .out1 _ _ ((preserved channel).symm.trans reference)
                    ((preserved datum).symm.trans call)
  | _, _, environment, source, target, preserved,
      .op .out2 (.cons channel (.cons first (.cons second .nil))), typed => by
      cases channel with
      | op op args => cases op
      | var channel =>
          cases first with
          | op op args => cases op
          | var first =>
              cases second with
              | op op args => cases op
              | var second =>
                  cases typed with
                  | out2 _ _ _ call reference result =>
                      exact .out2 _ _ _ ((preserved channel).symm.trans call)
                        ((preserved first).symm.trans reference) ((preserved second).symm.trans result)
  | _, _, environment, source, target, preserved, .op .nu (.cons body .nil), typed => by
      cases typed with
      | nu fresh bodyTyped =>
          exact .nu fresh (Typed.reflectRename (liftRen environment [.nm])
            (extendRole fresh source) (extendRole fresh target)
            (extend_roles_preserved _ _ _ preserved fresh) body bodyTyped)
  | _, _, environment, source, target, preserved, .op .rep (.cons body .nil), typed => by
      cases typed with
      | rep bodyTyped => exact .rep (Typed.reflectRename environment source target preserved body bodyTyped)
termination_by _ _ _ _ _ _ process _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem Typed.rename_iff {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (source : Roles Γ) (target : Roles Δ)
    (preserved : ∀ name, target (environment _ name) = source name) (process : Proc Γ) :
    Typed target (Mettapedia.OSLF.Binding.rename environment process) ↔ Typed source process :=
  ⟨Typed.reflectRename environment source target preserved process,
    fun typed => typed.rename environment preserved⟩

theorem Typed.weaken_iff {Γ : Ctx sig} (roles : Roles Γ) (fresh : Role) (process : Proc Γ) :
    Typed (extendRole fresh roles) (weaken (t := Srt.nm) process) ↔ Typed roles process :=
  Typed.rename_iff (fun _ name => .succ name) roles (extendRole fresh roles) (fun _ => rfl) process

theorem Typed.par_iff {Γ : Ctx sig} (roles : Roles Γ) (first second : Proc Γ) :
    Typed roles (Mettapedia.Languages.ProcessCalculi.PolyadicPi.par first second) ↔ Typed roles first ∧ Typed roles second := by
  constructor
  · intro typed
    cases typed with
    | par firstTyped secondTyped => exact ⟨firstTyped, secondTyped⟩
  · rintro ⟨firstTyped, secondTyped⟩
    exact .par firstTyped secondTyped

theorem Typed.unused_private_iff {Γ : Ctx sig} (roles : Roles Γ) (process : Proc Γ) :
    Typed roles (Mettapedia.Languages.ProcessCalculi.PolyadicPi.nu (weaken process)) ↔ Typed roles process := by
  constructor
  · intro typed
    cases typed with
    | nu fresh bodyTyped => exact (Typed.weaken_iff roles fresh process).1 bodyTyped
  · intro typed
    exact .nu .call ((Typed.weaken_iff roles .call process).2 typed)

theorem Typed.private_parallel_iff {Γ : Ctx sig} (roles : Roles Γ)
    (process : Proc (.nm :: Γ)) (frame : Proc Γ) :
    Typed roles (Mettapedia.Languages.ProcessCalculi.PolyadicPi.par
      (Mettapedia.Languages.ProcessCalculi.PolyadicPi.nu process) frame) ↔
      Typed roles (Mettapedia.Languages.ProcessCalculi.PolyadicPi.nu
        (Mettapedia.Languages.ProcessCalculi.PolyadicPi.par process (weaken frame))) := by
  constructor
  · intro typed
    cases typed with
    | par privateTyped frameTyped =>
        cases privateTyped with
        | nu fresh bodyTyped =>
            exact .nu fresh (.par bodyTyped ((Typed.weaken_iff roles fresh frame).2 frameTyped))
  · intro typed
    cases typed with
    | nu fresh bodyTyped =>
        cases bodyTyped with
        | par processTyped frameTyped =>
            exact .par (.nu fresh processTyped) ((Typed.weaken_iff roles fresh frame).1 frameTyped)

theorem Typed.private_exchange {Γ : Ctx sig} {roles : Roles Γ}
    {process : Proc (.nm :: .nm :: Γ)} (typed : Typed roles (Mettapedia.Languages.ProcessCalculi.PolyadicPi.nu (Mettapedia.Languages.ProcessCalculi.PolyadicPi.nu process))) :
    Typed roles (Mettapedia.Languages.ProcessCalculi.PolyadicPi.nu (Mettapedia.Languages.ProcessCalculi.PolyadicPi.nu (Mettapedia.OSLF.Binding.rename swapRen process))) := by
  cases typed with
  | nu outer middleTyped =>
      cases middleTyped with
      | nu inner bodyTyped =>
          apply Typed.nu inner
          apply Typed.nu outer
          apply bodyTyped.rename swapRen
          intro name
          cases name with
          | zero => rfl
          | succ name => cases name <;> rfl

theorem Typed.private_exchange_iff {Γ : Ctx sig} (roles : Roles Γ)
    (process : Proc (.nm :: .nm :: Γ)) :
    Typed roles (Mettapedia.Languages.ProcessCalculi.PolyadicPi.nu (Mettapedia.Languages.ProcessCalculi.PolyadicPi.nu process)) ↔ Typed roles (Mettapedia.Languages.ProcessCalculi.PolyadicPi.nu (Mettapedia.Languages.ProcessCalculi.PolyadicPi.nu (Mettapedia.OSLF.Binding.rename swapRen process))) := by
  constructor
  · exact Typed.private_exchange
  · intro typed
    have exchanged := typed.private_exchange
    rw [rename_exchange_involutive] at exchanged
    exact exchanged

theorem Typed.replication_iff {Γ : Ctx sig} (roles : Roles Γ) (process : Proc Γ) :
    Typed roles (Mettapedia.Languages.ProcessCalculi.PolyadicPi.rep process) ↔ Typed roles (Mettapedia.Languages.ProcessCalculi.PolyadicPi.par process (Mettapedia.Languages.ProcessCalculi.PolyadicPi.rep process)) := by
  constructor
  · intro typed
    cases typed with
    | rep bodyTyped => exact .par bodyTyped (.rep bodyTyped)
  · intro typed
    cases typed with
    | par bodyTyped _ => exact .rep bodyTyped

/-- All current structural equations preserve and reflect role typing,
including changes to unused and exchanged private-role assignments. -/
theorem Typed.structural_iff {Γ : Ctx sig} (roles : Roles Γ)
    {source target : Proc Γ} (equal : StructuralEq source target) :
    Typed roles source ↔ Typed roles target := by
  induction equal with
  | refl => exact Iff.rfl
  | symm _ ih => exact (ih roles).symm
  | trans _ _ firstIH secondIH => exact (firstIH roles).trans (secondIH roles)
  | parComm first second =>
      rw [Typed.par_iff, Typed.par_iff]
      exact and_comm
  | parAssoc first second third =>
      simp only [Typed.par_iff]
      exact and_assoc
  | parUnit process =>
      rw [Typed.par_iff]
      exact ⟨fun typed => typed.1, fun typed => ⟨typed, .nil _⟩⟩
  | nuUnused process => exact Typed.unused_private_iff roles process
  | nuPar process frame => exact Typed.private_parallel_iff roles process frame
  | nuSwap process => exact Typed.private_exchange_iff roles process
  | repUnfold process => exact Typed.replication_iff roles process
  | par _ _ firstIH secondIH =>
      rw [Typed.par_iff, Typed.par_iff]
      exact and_congr (firstIH roles) (secondIH roles)
  | nu _ ih =>
      constructor
      · intro typed
        cases typed with
        | nu fresh bodyTyped => exact .nu fresh ((ih (extendRole fresh roles)).1 bodyTyped)
      · intro typed
        cases typed with
        | nu fresh bodyTyped => exact .nu fresh ((ih (extendRole fresh roles)).2 bodyTyped)
  | inp1 channel _ ih =>
      constructor
      · intro typed
        cases typed with
        | inp1 name reference bodyTyped => exact .inp1 _ reference ((ih (extendRole .call roles)).1 bodyTyped)
      · intro typed
        cases typed with
        | inp1 name reference bodyTyped => exact .inp1 _ reference ((ih (extendRole .call roles)).2 bodyTyped)
  | inp2 channel _ ih =>
      constructor
      · intro typed
        cases typed with
        | inp2 name call bodyTyped => exact .inp2 _ call ((ih (pairRoles roles)).1 bodyTyped)
      · intro typed
        cases typed with
        | inp2 name call bodyTyped => exact .inp2 _ call ((ih (pairRoles roles)).2 bodyTyped)
  | rep _ ih =>
      constructor
      · intro typed
        cases typed with
        | rep bodyTyped => exact .rep ((ih roles).1 bodyTyped)
      · intro typed
        cases typed with
        | rep bodyTyped => exact .rep ((ih roles).2 bodyTyped)

/-- The supplied actual endpoint, including its structural representative,
retains the source's role assignment. This is subject reduction for the
original unary/binary interpretation, before the unary protocol lowering. -/
theorem Typed.modulo_step {Γ : Ctx sig} {roles : Roles Γ} {source target : Proc Γ}
    (typed : Typed roles source) (step : StepModulo source target) : Typed roles target := by
  obtain ⟨redex, contractum, before, firing, after⟩ := step
  exact (Typed.structural_iff roles after).1
    (((Typed.structural_iff roles before).1 typed).raw_step firing)

/-- Every supplied finite execution retains its initial channel roles at
the actual final representative. Paths use the existing operational GSLT. -/
theorem Typed.execution_endpoint {Γ : Ctx sig} {roles : Roles Γ}
    {source target : Proc Γ} (typed : Typed roles source)
    (path : Mettapedia.GSLT.IndexedOperational.ExecutionPath
      (NativeTypes.operationalTheory Γ) source target) : Typed roles target := by
  induction path with
  | refl => exact typed
  | cons step rest ih => exact ih (typed.modulo_step step.down)

/-- Every actual intermediate state of the retained path carries the same
role assignment. A prefix/suffix split identifies the visited occurrence;
it does not replace the supplied execution with another reachable path. -/
theorem Typed.execution_visited {Γ : Ctx sig} {roles : Roles Γ}
    {source target : Proc Γ} (typed : Typed roles source)
    (path : Mettapedia.GSLT.IndexedOperational.ExecutionPath
      (NativeTypes.operationalTheory Γ) source target) {middle : Proc Γ}
    (earlier : Mettapedia.GSLT.IndexedOperational.ExecutionPath
      (NativeTypes.operationalTheory Γ) source middle)
    (later : Mettapedia.GSLT.IndexedOperational.ExecutionPath
      (NativeTypes.operationalTheory Γ) middle target)
    (_split : path = earlier.append later) : Typed roles middle :=
  typed.execution_endpoint earlier

/-- A fresh external result gives every source expression a role-disciplined
compiler image, and every actual execution of that image retains the roles. -/
theorem fresh_result_compilation_execution_roles {Γ : Ctx sig} (term : Expr Γ)
    {target : Proc (.nm :: Γ)}
    (path : Mettapedia.GSLT.IndexedOperational.ExecutionPath
      (NativeTypes.operationalTheory (.nm :: Γ))
      (compile term (fun _ name => .succ name) .zero) target) :
    Typed (canonicalRoles Γ) target :=
  (fresh_result_compile_typed term).execution_endpoint path

theorem unary_output_roles {Γ : Ctx sig} (roles : Roles Γ)
    (channel datum : Var Γ .nm) (typed : Typed roles (out1 (.var channel) (.var datum))) :
    roles channel = .reference ∧ roles datum = .call := by
  cases typed with
  | out1 _ _ reference call => exact ⟨reference, call⟩

theorem binary_output_roles {Γ : Ctx sig} (roles : Roles Γ)
    (channel first second : Var Γ .nm)
    (typed : Typed roles (out2 (.var channel) (.var first) (.var second))) :
    roles channel = .call ∧ roles first = .reference ∧ roles second = .call := by
  cases typed with
  | out2 _ _ _ call reference result => exact ⟨call, reference, result⟩

theorem unary_input_role {Γ : Ctx sig} (roles : Roles Γ) (channel : Var Γ .nm)
    (body : Proc (.nm :: Γ)) (typed : Typed roles (inp1 (.var channel) body)) :
    roles channel = .reference := by
  cases typed with
  | inp1 _ reference _ => exact reference

theorem binary_input_role {Γ : Ctx sig} (roles : Roles Γ) (channel : Var Γ .nm)
    (body : Proc (.nm :: .nm :: Γ)) (typed : Typed roles (inp2 (.var channel) body)) :
    roles channel = .call := by
  cases typed with
  | inp2 _ call _ => exact call

/-- A single role assignment excludes the untyped unary-output/binary-input
cross-arity pair before protocol lowering. -/
theorem no_mixed_arity_pair {Γ : Ctx sig} (roles : Roles Γ)
    (channel datum : Var Γ .nm) (body : Proc (.nm :: .nm :: Γ)) :
    ¬ Typed roles (par (out1 (.var channel) (.var datum)) (inp2 (.var channel) body)) := by
  intro typed
  cases typed with
  | par output input =>
      have reference := (unary_output_roles roles channel datum output).1
      have call := binary_input_role roles channel body input
      rw [reference] at call
      cases call

theorem no_reverse_mixed_arity_pair {Γ : Ctx sig} (roles : Roles Γ)
    (channel first second : Var Γ .nm) (body : Proc (.nm :: Γ)) :
    ¬ Typed roles (par (out2 (.var channel) (.var first) (.var second))
      (inp1 (.var channel) body)) := by
  intro typed
  cases typed with
  | par output input =>
      have call := (binary_output_roles roles channel first second output).1
      have reference := unary_input_role roles channel body input
      rw [reference] at call
      cases call

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingChannelRoles
