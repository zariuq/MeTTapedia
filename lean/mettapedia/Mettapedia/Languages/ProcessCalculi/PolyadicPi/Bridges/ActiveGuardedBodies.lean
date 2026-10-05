import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarkedNames
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredEquations

/-!
# Traced active observations retain suspended bodies modulo the equations

Header observations record subjects and ordered output fields. This refinement
also records each input's actual body in the existing equational quotient,
after the supplied sorted reindexing. Structural transport preserves these
observations, including congruence inside input guards. The interpretation of
private binder marks need not be injective: no equality of names is inferred
merely from two equal binder marks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveGuardedBodies

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredEquations
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveHeaderInvariant

universe u

structure Observation (Label : Type u) (Ω : Ctx sig) where
  header : ActiveMarkedNames.Observation Label (Var Ω Srt.nm)
  unaryBody : Option (TermQ equations (.nm :: Ω) .pr)
  binaryBody : Option (TermQ equations (.nm :: .nm :: Ω) .pr)

def bodyQ {Γ Ω : Ctx sig} (environment : Ren sig Γ Ω) (binders : List Srt)
    (body : Proc (binders ++ Γ)) : TermQ equations (binders ++ Ω) .pr :=
  Quotient.mk _ (rename (liftRen environment binders) body)

def input1 {Label : Type u} {Γ Ω : Ctx sig} (origin : Label)
    (channel : Name Γ) (body : Proc (.nm :: Γ)) (environment : Ren sig Γ Ω) : Observation Label Ω :=
  ⟨⟨.input1, origin, ActiveMarkedNames.nameKey (environment .nm) channel, []⟩,
    some (bodyQ environment [.nm] body), none⟩

def input2 {Label : Type u} {Γ Ω : Ctx sig} (origin : Label)
    (channel : Name Γ) (body : Proc (.nm :: .nm :: Γ)) (environment : Ren sig Γ Ω) : Observation Label Ω :=
  ⟨⟨.input2, origin, ActiveMarkedNames.nameKey (environment .nm) channel, []⟩,
    none, some (bodyQ environment [.nm, .nm] body)⟩

def output1 {Label : Type u} {Γ Ω : Ctx sig} (origin : Label)
    (channel datum : Name Γ) (environment : Ren sig Γ Ω) : Observation Label Ω :=
  ⟨⟨.output1, origin, ActiveMarkedNames.nameKey (environment .nm) channel,
    [ActiveMarkedNames.nameKey (environment .nm) datum]⟩, none, none⟩

def output2 {Label : Type u} {Γ Ω : Ctx sig} (origin : Label)
    (channel first second : Name Γ) (environment : Ren sig Γ Ω) : Observation Label Ω :=
  ⟨⟨.output2, origin, ActiveMarkedNames.nameKey (environment .nm) channel,
    [ActiveMarkedNames.nameKey (environment .nm) first,
      ActiveMarkedNames.nameKey (environment .nm) second]⟩, none, none⟩

def observe {Label : Type u} {Ω : Ctx sig} (binderName : Label → Var Ω .nm) :
    {Γ : Ctx sig} → ActiveMarking.Tree Label → Proc Γ → Ren sig Γ Ω → Set (Observation Label Ω)
  | _, _, .var _, _ => ∅
  | _, _, .op .nil .nil, _ => ∅
  | _, marked, .op .par (.cons first (.cons second .nil)), environment => match marked with
      | .par left right => observe binderName left first environment ∪ observe binderName right second environment
      | _ => ∅
  | _, marked, .op .inp1 (.cons channel (.cons body .nil)), environment => match marked with
      | .inp1 origin _ => {input1 origin channel body environment}
      | _ => ∅
  | _, marked, .op .inp2 (.cons channel (.cons body .nil)), environment => match marked with
      | .inp2 origin _ => {input2 origin channel body environment}
      | _ => ∅
  | _, marked, .op .out1 (.cons channel (.cons datum .nil)), environment => match marked with
      | .out1 origin => {output1 origin channel datum environment}
      | _ => ∅
  | _, marked, .op .out2 (.cons channel (.cons first (.cons second .nil))), environment => match marked with
      | .out2 origin => {output2 origin channel first second environment}
      | _ => ∅
  | _, marked, .op .nu (.cons body .nil), environment => match marked with
      | .nu origin inner => observe binderName inner body (prependRen (binderName origin) environment)
      | _ => ∅
  | _, marked, .op .rep (.cons body .nil), environment => match marked with
      | .rep inner => observe binderName inner body environment
      | _ => ∅
termination_by _ _marked process _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

private theorem nameKey_comp {Γ Δ Ω : Ctx sig} (reindex : Ren sig Γ Δ)
    (environment : Ren sig Δ Ω) (name : Name Γ) :
    ActiveMarkedNames.nameKey (environment .nm) (rename reindex name) =
      ActiveMarkedNames.nameKey (fun name => environment .nm (reindex .nm name)) name := by
  cases name with
  | var name => rfl
  | op operator _ => cases operator

theorem bodyQ_rename {Γ Δ Ω : Ctx sig} (reindex : Ren sig Γ Δ)
    (environment : Ren sig Δ Ω) (binders : List Srt) (body : Proc (binders ++ Γ)) :
    bodyQ environment binders (rename (liftRen reindex binders) body) =
      bodyQ (fun sort name => environment sort (reindex sort name)) binders body := by
  simp only [bodyQ, rename_comp]
  rw [← liftRen_comp reindex environment binders]

private theorem extension_comp {Γ Δ Ω : Ctx sig} (reindex : Ren sig Γ Δ)
    (environment : Ren sig Δ Ω) (fresh : Var Ω .nm) :
    (fun sort name => prependRen fresh environment sort (liftRen reindex [.nm] sort name)) =
      prependRen fresh (fun sort name => environment sort (reindex sort name)) := by
  funext sort name
  cases name <;> rfl

theorem observe_rename {Label : Type u} {Ω : Ctx sig} (binderName : Label → Var Ω .nm) :
    ∀ {Γ Δ : Ctx sig} (reindex : Ren sig Γ Δ) (process : Proc Γ) (marked : ActiveMarking.Tree Label)
      (environment : Ren sig Δ Ω),
      observe binderName marked (rename reindex process) environment =
        observe binderName marked process (fun sort name => environment sort (reindex sort name))
  | _, _, _, .var _, _, _ => by simp only [rename, observe]
  | _, _, _, .op .nil .nil, _, _ => by simp only [rename, renameArgs, observe]
  | _, _, reindex, .op .par (.cons first (.cons second .nil)), marked, environment => by
      cases marked <;> simp only [rename, renameArgs, liftRen, observe]
      rename_i left right
      rw [observe_rename binderName reindex first left environment,
        observe_rename binderName reindex second right environment]
  | _, _, reindex, .op .inp1 (.cons channel (.cons body .nil)), marked, environment => by
      cases marked <;> simp only [rename, renameArgs, liftRen, observe]
      simp only [input1]
      rw [nameKey_comp reindex environment channel, bodyQ_rename reindex environment [.nm] body]
  | _, _, reindex, .op .inp2 (.cons channel (.cons body .nil)), marked, environment => by
      cases marked <;> simp only [rename, renameArgs, liftRen, observe]
      simp only [input2]
      rw [nameKey_comp reindex environment channel, bodyQ_rename reindex environment [.nm, .nm] body]
  | _, _, reindex, .op .out1 (.cons channel (.cons datum .nil)), marked, environment => by
      cases marked <;> simp only [rename, renameArgs, liftRen, observe]
      simp only [output1]
      rw [nameKey_comp reindex environment channel, nameKey_comp reindex environment datum]
  | _, _, reindex, .op .out2 (.cons channel (.cons first (.cons second .nil))), marked, environment => by
      cases marked <;> simp only [rename, renameArgs, liftRen, observe]
      simp only [output2]
      rw [nameKey_comp reindex environment channel, nameKey_comp reindex environment first,
        nameKey_comp reindex environment second]
  | _, _, reindex, .op .nu (.cons body .nil), marked, environment => by
      cases marked <;> simp only [rename, renameArgs, observe]
      rename_i origin inner
      rw [observe_rename binderName (liftRen reindex [.nm]) body inner _, extension_comp]
  | _, _, reindex, .op .rep (.cons body .nil), marked, environment => by
      cases marked <;> simp only [rename, renameArgs, liftRen, observe]
      rename_i inner
      exact observe_rename binderName reindex body inner environment
termination_by _ _ _ process _ _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem bodyQ_structural {Γ Ω : Ctx sig} (environment : Ren sig Γ Ω) (binders : List Srt)
    {first second : Proc (binders ++ Γ)} (equal : StructuralEq first second) :
    bodyQ environment binders first = bodyQ environment binders second :=
  Quotient.sound (structuralEq_complete (equal.rename (liftRen environment binders)))

/-- The actual guard body is transported in the existing equation quotient,
not replaced by a body having only the same prefix shape. -/
theorem observations_back {Label : Type u} {Ω : Ctx sig}
    (binderName : Label → Var Ω .nm) {Γ : Ctx sig} {m n : ActiveMarking.Tree Label} {p q : Proc Γ}
    (tracked : Transport m p n q) :
    ∀ environment : Ren sig Γ Ω,
      observe binderName n q environment ⊆ observe binderName m p environment := by
  induction tracked with
  | refl => intro environment; exact Set.Subset.refl _
  | trans _ _ firstIH secondIH => intro environment; exact (secondIH environment).trans (firstIH environment)
  | parComm => intro environment; simp only [par, observe, Set.union_comm, Set.Subset.refl]
  | parAssoc => intro environment; simp only [par, observe, Set.union_assoc, Set.Subset.refl]
  | parAssocBack => intro environment; simp only [par, observe, Set.union_assoc, Set.Subset.refl]
  | parUnit => intro environment; simp only [par, nil, observe, Set.union_empty, Set.Subset.refl]
  | parUnitBack => intro environment; simp only [par, nil, observe, Set.union_empty, Set.Subset.refl]
  | nuUnused origin marked process =>
      intro environment
      simp only [nu, observe, weaken]
      rw [observe_rename]
      exact Set.Subset.refl _
  | nuUnusedBack origin marked process =>
      intro environment
      simp only [nu, observe, weaken]
      rw [observe_rename]
      exact Set.Subset.refl _
  | nuPar origin first second process frame =>
      intro environment
      simp only [nu, par, observe, weaken]
      rw [observe_rename]
      exact Set.Subset.refl _
  | nuParBack origin first second process frame =>
      intro environment
      simp only [nu, par, observe, weaken]
      rw [observe_rename]
      exact Set.Subset.refl _
  | nuSwap outer inner marked process =>
      intro environment
      simp only [nu, observe]
      rw [observe_rename]
      have environmentEq :
          (fun sort name => prependRen (binderName outer) (prependRen (binderName inner) environment)
            sort (swapRen sort name)) =
          prependRen (binderName inner) (prependRen (binderName outer) environment) := by
        funext sort name
        cases name with
        | zero => rfl
        | succ name => cases name <;> rfl
      rw [environmentEq]
  | nuSwapBack outer inner marked process =>
      intro environment
      simp only [nu, observe]
      rw [observe_rename]
      have environmentEq :
          (fun sort name => prependRen (binderName outer) (prependRen (binderName inner) environment)
            sort (swapRen sort name)) =
          prependRen (binderName inner) (prependRen (binderName outer) environment) := by
        funext sort name
        cases name with
        | zero => rfl
        | succ name => cases name <;> rfl
      rw [environmentEq]
  | repUnfold => intro environment; simp only [rep, par, observe, Set.union_self, Set.Subset.refl]
  | repFold => intro environment; simp only [rep, par, observe]; exact Set.subset_union_right
  | par _ _ firstIH secondIH =>
      intro environment
      simp only [par, observe]
      exact Set.union_subset_union (firstIH environment) (secondIH environment)
  | nu origin _ ih => intro environment; simp only [nu, observe]; exact ih _
  | inp1 origin channel equal _ =>
      intro environment
      simp only [inp1, observe, input1]
      rw [bodyQ_structural environment [.nm] equal.erase]
  | inp2 origin channel equal _ =>
      intro environment
      simp only [inp2, observe, input2]
      rw [bodyQ_structural environment [.nm, .nm] equal.erase]
  | rep _ ih => intro environment; simp only [rep, observe]; exact ih environment

def scopeEnvironment {Label : Type u} {Ω : Ctx sig} (binderName : Label → Var Ω .nm) :
    {Γ Δ : Ctx sig} → {scope : ScopedActiveFrontier.Scope Γ Δ} →
    ScopeMarks Label scope → Ren sig Γ Ω → Ren sig Δ Ω
  | _, _, _, .nil, environment => environment
  | _, _, _, .bind origin rest, environment =>
      scopeEnvironment binderName rest (prependRen (binderName origin) environment)

theorem observe_scope {Label : Type u} {Ω : Ctx sig} (binderName : Label → Var Ω .nm) :
    ∀ {Γ Δ : Ctx sig} {scope : ScopedActiveFrontier.Scope Γ Δ}
      (binders : ScopeMarks Label scope) (marked : ActiveMarking.Tree Label)
      (body : Proc Δ) (environment : Ren sig Γ Ω),
      observe binderName (binders.close marked) (scope.close body) environment =
        observe binderName marked body (scopeEnvironment binderName binders environment)
  | _, _, _, .nil, _, _, _ => rfl
  | _, _, _, .bind origin rest, marked, body, environment => by
      simp only [ScopeMarks.close, ScopedActiveFrontier.Scope.close, nu, observe, scopeEnvironment]
      exact observe_scope binderName rest marked body (prependRen (binderName origin) environment)

def inputObservation {Label : Type u} {Ω : Ctx sig} : {Γ : Ctx sig} →
    {redex reduct : Proc Γ} → {selected : ScopedCommunicationInversion.Communication redex reduct} →
    {marked : ActiveMarking.Tree Label} → MarkedCommunication selected marked →
      Ren sig Γ Ω → Observation Label Ω
  | _, _, _, _, _, .unary channel _ body _ origin _ _, environment => input1 origin channel body environment
  | _, _, _, _, _, .binary channel _ _ body _ origin _ _, environment => input2 origin channel body environment

def outputObservation {Label : Type u} {Ω : Ctx sig} : {Γ : Ctx sig} →
    {redex reduct : Proc Γ} → {selected : ScopedCommunicationInversion.Communication redex reduct} →
    {marked : ActiveMarking.Tree Label} → MarkedCommunication selected marked →
      Ren sig Γ Ω → Observation Label Ω
  | _, _, _, _, _, .unary channel datum _ origin _ _ _, environment => output1 origin channel datum environment
  | _, _, _, _, _, .binary channel first second _ origin _ _ _, environment => output2 origin channel first second environment

/-- A unary firing observes its original suspended body and input occurrence. -/
theorem unary_input_observation {Label : Type u} {Γ Ω : Ctx sig}
    (channel datum : Name Γ) (body : Proc (.nm :: Γ))
    {marked : ActiveMarking.Tree Label}
    (comm : MarkedCommunication
      (ScopedCommunicationInversion.Communication.unary channel datum body) marked)
    (environment : Ren sig Γ Ω) :
    inputObservation comm environment = input1 comm.inputOrigin channel body environment := by
  cases comm
  rfl

/-- A unary firing observes its original output occurrence and payload. -/
theorem unary_output_observation {Label : Type u} {Γ Ω : Ctx sig}
    (channel datum : Name Γ) (body : Proc (.nm :: Γ))
    {marked : ActiveMarking.Tree Label}
    (comm : MarkedCommunication
      (ScopedCommunicationInversion.Communication.unary channel datum body) marked)
    (environment : Ren sig Γ Ω) :
    outputObservation comm environment = output1 comm.outputOrigin channel datum environment := by
  cases comm
  rfl

theorem communication_subjects_agree {Label : Type u} {Ω Γ : Ctx sig}
    {redex reduct : Proc Γ} {selected : ScopedCommunicationInversion.Communication redex reduct}
    {marked : ActiveMarking.Tree Label} (comm : MarkedCommunication selected marked) (environment : Ren sig Γ Ω) :
    (inputObservation comm environment).header.channel = (outputObservation comm environment).header.channel := by
  cases comm <;> rfl

theorem communication_input_observed {Label : Type u} {Ω : Ctx sig}
    (binderName : Label → Var Ω .nm) {Γ : Ctx sig} {redex reduct : Proc Γ}
    {selected : ScopedCommunicationInversion.Communication redex reduct}
    {marked : ActiveMarking.Tree Label} (comm : MarkedCommunication selected marked)
    (environment : Ren sig Γ Ω) :
    inputObservation comm environment ∈ observe binderName marked redex environment := by
  cases comm <;> simp only [inputObservation, par, inp1, inp2, out1, out2, observe,
    Set.mem_union, Set.mem_singleton_iff]
  all_goals exact Or.inr True.intro

theorem communication_output_observed {Label : Type u} {Ω : Ctx sig}
    (binderName : Label → Var Ω .nm) {Γ : Ctx sig} {redex reduct : Proc Γ}
    {selected : ScopedCommunicationInversion.Communication redex reduct}
    {marked : ActiveMarking.Tree Label} (comm : MarkedCommunication selected marked)
    (environment : Ren sig Γ Ω) :
    outputObservation comm environment ∈ observe binderName marked redex environment := by
  cases comm <;> simp only [outputObservation, par, inp1, inp2, out1, out2, observe,
    Set.mem_union, Set.mem_singleton_iff]
  all_goals exact Or.inl True.intro

theorem traced_input_observed {Label : Type u} {Ω : Ctx sig} (binderName : Label → Var Ω .nm)
    {Γ : Ctx sig} {original : ActiveMarking.Tree Label} {source target : Proc Γ}
    {exposure : ScopedCommunicationInversion.Exposure source target}
    (traced : TracedExposure original exposure) (environment : Ren sig Γ Ω) :
    inputObservation traced.continuation (scopeEnvironment binderName traced.binders environment) ∈
      observe binderName original source environment := by
  apply observations_back binderName traced.transport environment
  rw [observe_scope]
  simp only [par, observe, Set.mem_union]
  exact Or.inl (communication_input_observed binderName traced.continuation _)

theorem traced_output_observed {Label : Type u} {Ω : Ctx sig} (binderName : Label → Var Ω .nm)
    {Γ : Ctx sig} {original : ActiveMarking.Tree Label} {source target : Proc Γ}
    {exposure : ScopedCommunicationInversion.Exposure source target}
    (traced : TracedExposure original exposure) (environment : Ren sig Γ Ω) :
    outputObservation traced.continuation (scopeEnvironment binderName traced.binders environment) ∈
      observe binderName original source environment := by
  apply observations_back binderName traced.transport environment
  rw [observe_scope]
  simp only [par, observe, Set.mem_union]
  exact Or.inl (communication_output_observed binderName traced.continuation _)

private theorem names_equal_of_keys {Γ Δ Ω : Ctx sig} (left : Ren sig Γ Ω)
    (right : Ren sig Δ Ω) (first : Name Γ) (second : Name Δ)
    (same : ActiveMarkedNames.nameKey (left .nm) first =
      ActiveMarkedNames.nameKey (right .nm) second) : rename left first = rename right second := by
  cases first with
  | var first =>
      cases second with
      | var second => exact congrArg Term.var same
      | op operator _ => cases operator
  | op operator _ => cases operator

/-- Equal observed unary guards and the same observed datum imply equality
of the actual opened bodies modulo the authored equations. -/
theorem unary_opening {Label : Type u} {Γ Δ Ω : Ctx sig}
    (origin other : Label) (channel : Name Γ) (otherChannel : Name Δ)
    (body : Proc (.nm :: Γ)) (otherBody : Proc (.nm :: Δ))
    (environment : Ren sig Γ Ω) (otherEnvironment : Ren sig Δ Ω)
    (datum : Name Γ) (otherDatum : Name Δ)
    (guard : input1 origin channel body environment =
      input1 other otherChannel otherBody otherEnvironment)
    (field : ActiveMarkedNames.nameKey (environment .nm) datum =
      ActiveMarkedNames.nameKey (otherEnvironment .nm) otherDatum) :
    EqClosure equations (rename environment (inst body datum))
      (rename otherEnvironment (inst otherBody otherDatum)) := by
  have bodies : bodyQ environment [.nm] body = bodyQ otherEnvironment [.nm] otherBody :=
    Option.some.inj (congrArg Observation.unaryBody guard)
  have bodyEq : EqClosure equations (rename (liftRen environment [.nm]) body)
      (rename (liftRen otherEnvironment [.nm]) otherBody) := Quotient.exact bodies
  rw [rename_inst, rename_inst, names_equal_of_keys environment otherEnvironment datum otherDatum field]
  exact eqClosure_inst bodyEq (.refl _)

/-- Binary readback keeps the supplied first and second field order when
opening the original suspended continuation. -/
theorem binary_opening {Label : Type u} {Γ Δ Ω : Ctx sig}
    (origin other : Label) (channel : Name Γ) (otherChannel : Name Δ)
    (body : Proc (.nm :: .nm :: Γ)) (otherBody : Proc (.nm :: .nm :: Δ))
    (environment : Ren sig Γ Ω) (otherEnvironment : Ren sig Δ Ω)
    (first second : Name Γ) (otherFirst otherSecond : Name Δ)
    (guard : input2 origin channel body environment =
      input2 other otherChannel otherBody otherEnvironment)
    (firstField : ActiveMarkedNames.nameKey (environment .nm) first =
      ActiveMarkedNames.nameKey (otherEnvironment .nm) otherFirst)
    (secondField : ActiveMarkedNames.nameKey (environment .nm) second =
      ActiveMarkedNames.nameKey (otherEnvironment .nm) otherSecond) :
    EqClosure equations (rename environment (openPair body first second))
      (rename otherEnvironment (openPair otherBody otherFirst otherSecond)) := by
  have bodies : bodyQ environment [.nm, .nm] body = bodyQ otherEnvironment [.nm, .nm] otherBody :=
    Option.some.inj (congrArg Observation.binaryBody guard)
  have bodyEq : EqClosure equations (rename (liftRen environment [.nm, .nm]) body)
      (rename (liftRen otherEnvironment [.nm, .nm]) otherBody) := Quotient.exact bodies
  rw [rename_openPair, rename_openPair,
    names_equal_of_keys environment otherEnvironment first otherFirst firstField,
    names_equal_of_keys environment otherEnvironment second otherSecond secondField]
  exact eqClosure_bind _ bodyEq

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveGuardedBodies
