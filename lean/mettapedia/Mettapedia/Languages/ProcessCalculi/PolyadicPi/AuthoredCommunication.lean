import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Basic

/-!
# Exact open instances of the authored polyadic communication schemas

The target of the name-passing lambda compiler uses these actual intrinsic
rewrite declarations. The comparisons retain the supplied continuation and
all ambient variables, including variables below both binary receiver names.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredCommunication

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ContextualRootEvents
open Mettapedia.OSLF.Binding.ContextualAssignment
open Mettapedia.Languages.ProcessCalculi.PolyadicPi

def supply {Γ : Ctx sig} (unary : Proc (.nm :: Γ))
    (binary : Proc (.nm :: .nm :: Γ)) : ContextualAssignment sig metas Γ
  | ⟨0, _⟩ => unary
  | ⟨1, _⟩ => binary
  | ⟨n + 2, impossible⟩ => by simp [metas] at impossible

@[simp] theorem supply_zero {Γ : Ctx sig} (unary : Proc (.nm :: Γ))
    (binary : Proc (.nm :: .nm :: Γ)) : supply unary binary 0 = unary := rfl
@[simp] theorem supply_one {Γ : Ctx sig} (unary : Proc (.nm :: Γ))
    (binary : Proc (.nm :: .nm :: Γ)) : supply unary binary 1 = binary := rfl

def close1 {Γ : Ctx sig} (channel datum : Name Γ) : Sub sig [.nm, .nm] Γ :=
  argsToSub (.cons channel (.cons datum .nil))

def close2 {Γ : Ctx sig} (channel first second : Name Γ) : Sub sig [.nm, .nm, .nm] Γ :=
  argsToSub (.cons channel (.cons first (.cons second .nil)))

def unaryInstance {Γ : Ctx sig} (channel datum : Name Γ)
    (body : Proc (.nm :: Γ)) : Instance comm1 Γ where
  body := supply body nil
  close := close1 channel datum

def binaryInstance {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) : Instance comm2 Γ where
  body := supply nil body
  close := close2 channel first second

private theorem unary_identity {Γ : Ctx sig} :
    joinSub (S := sig) (Γ := Γ) (Δ := Srt.nm :: Γ) (dependencies := [Srt.nm])
      (argsToSub (Args.cons (Term.var .zero : Name (.nm :: Γ)) Args.nil))
      (weakenSub (S := sig) (Γ := Γ) (Δ := Γ) [Srt.nm]
        (fun _ x => Term.var x)) =
      (fun _ x => Term.var x) := by
  funext s x
  cases x with
  | zero => rfl
  | succ old => rfl

private theorem binary_identity {Γ : Ctx sig} :
    joinSub (S := sig) (Γ := Γ) (Δ := Srt.nm :: Srt.nm :: Γ)
      (dependencies := [Srt.nm, Srt.nm])
      (argsToSub (Args.cons (Term.var .zero : Name (.nm :: .nm :: Γ))
        (Args.cons (Term.var (.succ .zero) : Name (.nm :: .nm :: Γ)) Args.nil)))
      (weakenSub (S := sig) (Γ := Γ) (Δ := Γ) [Srt.nm, Srt.nm]
        (fun _ x => Term.var x)) =
      (fun _ x => Term.var x) := by
  funext s x
  cases x with
  | zero => rfl
  | succ x => cases x <;> rfl

private theorem unary_open {Γ : Ctx sig} (datum : Name Γ) :
    joinSub (dependencies := [Srt.nm]) (argsToSub (Args.cons datum Args.nil))
      (fun _ x => Term.var x : Sub sig Γ Γ) = extend datum := by
  funext s x
  cases x <;> rfl

private theorem binary_open {Γ : Ctx sig} (first second : Name Γ) :
    joinSub (dependencies := [Srt.nm, Srt.nm])
      (argsToSub (Args.cons first (Args.cons second Args.nil)))
      (fun _ x => Term.var x : Sub sig Γ Γ) = pairSub first second := by
  funext s x
  cases x with
  | zero => rfl
  | succ x => cases x <;> rfl

theorem unary_source {Γ : Ctx sig} (channel datum : Name Γ)
    (body : Proc (.nm :: Γ)) :
    (unaryInstance channel datum body).source =
      par (out1 channel datum) (inp1 channel body) := by
  simp only [Instance.source, unaryInstance, comm1, unaryContinuation,
    ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
    ContextualAssignment.apply, supply_zero,
    liftSub]
  change par (out1 channel datum)
    (inp1 channel (Mettapedia.OSLF.Binding.bind
      (joinSub (S := sig) (Γ := Γ) (Δ := Srt.nm :: Γ) (dependencies := [Srt.nm])
        (argsToSub (S := sig) (bs := [Srt.nm])
          (Args.cons (Term.var .zero : Name (Srt.nm :: Γ)) Args.nil))
        (weakenSub (S := sig) (Γ := Γ) (Δ := Γ) [Srt.nm] (fun _ x => Term.var x))) body)) = _
  rw [unary_identity, bind_id]

theorem unary_target {Γ : Ctx sig} (channel datum : Name Γ)
    (body : Proc (.nm :: Γ)) :
    (unaryInstance channel datum body).target = inst body datum := by
  simp only [Instance.target, unaryInstance, comm1, unaryContinuation,
    ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
    ContextualAssignment.apply, supply_zero,
    liftSub]
  change Mettapedia.OSLF.Binding.bind
    (joinSub (dependencies := [Srt.nm]) (argsToSub (Args.cons datum Args.nil))
    (fun _ x => Term.var x)) body = inst body datum
  rw [unary_open]
  rfl

theorem binary_source {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    (binaryInstance channel first second body).source =
      par (out2 channel first second) (inp2 channel body) := by
  simp only [Instance.source, binaryInstance, comm2, binaryContinuation,
    ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
    ContextualAssignment.apply, supply_one,
    liftSub]
  change par (out2 channel first second)
    (inp2 channel (Mettapedia.OSLF.Binding.bind
      (joinSub (S := sig) (Γ := Γ) (Δ := Srt.nm :: Srt.nm :: Γ)
        (dependencies := [Srt.nm, Srt.nm])
        (argsToSub (S := sig) (bs := [Srt.nm, Srt.nm])
          (Args.cons (Term.var .zero : Name (Srt.nm :: Srt.nm :: Γ))
            (Args.cons (Term.var (.succ .zero) : Name (Srt.nm :: Srt.nm :: Γ)) Args.nil)))
        (weakenSub (S := sig) (Γ := Γ) (Δ := Γ) [Srt.nm, Srt.nm]
          (fun _ x => Term.var x))) body)) = _
  rw [binary_identity, bind_id]

theorem binary_target {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    (binaryInstance channel first second body).target = openPair body first second := by
  simp only [Instance.target, binaryInstance, comm2, binaryContinuation,
    ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
    ContextualAssignment.apply, supply_one,
    liftSub]
  change Mettapedia.OSLF.Binding.bind
    (joinSub (dependencies := [Srt.nm, Srt.nm])
      (argsToSub (Args.cons first (Args.cons second Args.nil)))
    (fun _ x => Term.var x)) body = openPair body first second
  rw [binary_open]
  rfl

/-- Every independent unary COMM is an event of the declared intrinsic rule. -/
def unaryEvent {Γ : Ctx sig} (channel datum : Name Γ) (body : Proc (.nm :: Γ)) :
    Event comm1 (par (out1 channel datum) (inp1 channel body)) (inst body datum) where
  firing := unaryInstance channel datum body
  source_eq := unary_source channel datum body
  target_eq := unary_target channel datum body

/-- Every independent binary COMM has an authored event at its exact endpoints. -/
def binaryEvent {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    Event comm2 (par (out2 channel first second) (inp2 channel body))
      (openPair body first second) where
  firing := binaryInstance channel first second body
  source_eq := binary_source channel first second body
  target_eq := binary_target channel first second body

theorem arbitrary_unary_source {Γ : Ctx sig} (firing : Instance comm1 Γ) :
    firing.source =
      par (out1 (firing.close _ .zero) (firing.close _ (.succ .zero)))
        (inp1 (firing.close _ .zero) (firing.body 0)) := by
  simp only [Instance.source, comm1, unaryContinuation,
    ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
    ContextualAssignment.apply, liftSub]
  change par (out1 (firing.close _ .zero) (firing.close _ (.succ .zero)))
    (inp1 (firing.close _ .zero) (Mettapedia.OSLF.Binding.bind
      (joinSub (S := sig) (Γ := Γ) (Δ := Srt.nm :: Γ) (dependencies := [Srt.nm])
        (argsToSub (S := sig) (bs := [Srt.nm])
          (Args.cons (Term.var .zero : Name (Srt.nm :: Γ)) Args.nil))
        (weakenSub (S := sig) (Γ := Γ) (Δ := Γ) [Srt.nm]
          (fun _ x => Term.var x))) (firing.body 0))) = _
  rw [unary_identity, bind_id]

theorem arbitrary_unary_target {Γ : Ctx sig} (firing : Instance comm1 Γ) :
    firing.target = inst (firing.body 0) (firing.close _ (.succ .zero)) := by
  simp only [Instance.target, comm1, unaryContinuation,
    ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
    ContextualAssignment.apply, liftSub]
  change Mettapedia.OSLF.Binding.bind
    (joinSub (S := sig) (Γ := Γ) (Δ := Γ) (dependencies := [Srt.nm])
      (argsToSub (S := sig) (bs := [Srt.nm])
        (Args.cons (firing.close Srt.nm (.succ .zero)) Args.nil))
      (fun _ x => Term.var x)) (firing.body 0) = _
  rw [unary_open]
  rfl

theorem arbitrary_binary_source {Γ : Ctx sig} (firing : Instance comm2 Γ) :
    firing.source =
      par (out2 (firing.close _ .zero) (firing.close _ (.succ .zero))
        (firing.close _ (.succ (.succ .zero))))
        (inp2 (firing.close _ .zero) (firing.body 1)) := by
  simp only [Instance.source, comm2, binaryContinuation,
    ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
    ContextualAssignment.apply, liftSub]
  change par (out2 (firing.close _ .zero) (firing.close _ (.succ .zero))
      (firing.close _ (.succ (.succ .zero))))
    (inp2 (firing.close _ .zero) (Mettapedia.OSLF.Binding.bind
      (joinSub (S := sig) (Γ := Γ) (Δ := Srt.nm :: Srt.nm :: Γ)
        (dependencies := [Srt.nm, Srt.nm])
        (argsToSub (S := sig) (bs := [Srt.nm, Srt.nm])
          (Args.cons (Term.var .zero : Name (Srt.nm :: Srt.nm :: Γ))
            (Args.cons (Term.var (.succ .zero) : Name (Srt.nm :: Srt.nm :: Γ)) Args.nil)))
        (weakenSub (S := sig) (Γ := Γ) (Δ := Γ) [Srt.nm, Srt.nm]
          (fun _ x => Term.var x))) (firing.body 1))) = _
  rw [binary_identity, bind_id]

theorem arbitrary_binary_target {Γ : Ctx sig} (firing : Instance comm2 Γ) :
    firing.target = openPair (firing.body 1) (firing.close _ (.succ .zero))
      (firing.close _ (.succ (.succ .zero))) := by
  simp only [Instance.target, comm2, binaryContinuation,
    ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
    ContextualAssignment.apply, liftSub]
  change Mettapedia.OSLF.Binding.bind
    (joinSub (S := sig) (Γ := Γ) (Δ := Γ) (dependencies := [Srt.nm, Srt.nm])
      (argsToSub (S := sig) (bs := [Srt.nm, Srt.nm])
        (Args.cons (firing.close Srt.nm (.succ .zero))
        (Args.cons (firing.close Srt.nm (.succ (.succ .zero))) Args.nil)))
      (fun _ x => Term.var x)) (firing.body 1) = _
  rw [binary_open]
  rfl

/-- Every supplied unary firing, not just the canonical examples, is the
independent unary communication at its actual source and target. -/
theorem unary_firing_step {Γ : Ctx sig} (firing : Instance comm1 Γ) :
    Step firing.source firing.target := by
  rw [arbitrary_unary_source, arbitrary_unary_target]
  exact .comm1 _ _ _

theorem binary_firing_step {Γ : Ctx sig} (firing : Instance comm2 Γ) :
    Step firing.source firing.target := by
  rw [arbitrary_binary_source, arbitrary_binary_target]
  exact .comm2 _ _ _ _

/-- The contextual closure taken directly from the two authored schemas. -/
inductive AuthoredStep : {Γ : Ctx sig} → Proc Γ → Proc Γ → Prop where
  | unary {Γ} {source target : Proc Γ} : Event comm1 source target → AuthoredStep source target
  | binary {Γ} {source target : Proc Γ} : Event comm2 source target → AuthoredStep source target
  | parL {Γ} {p p' : Proc Γ} (q : Proc Γ) :
      AuthoredStep p p' → AuthoredStep (par p q) (par p' q)
  | parR {Γ} (p : Proc Γ) {q q' : Proc Γ} :
      AuthoredStep q q' → AuthoredStep (par p q) (par p q')
  | nu {Γ} {p p' : Proc (.nm :: Γ)} : AuthoredStep p p' → AuthoredStep (nu p) (nu p')

/-- All independent contextual transitions have an event of an authored
rule at the selected occurrence; every authored transition reflects back. -/
theorem authoredStep_iff {Γ : Ctx sig} (source target : Proc Γ) :
    AuthoredStep source target ↔ Step source target := by
  constructor
  · intro step
    induction step with
    | unary event =>
        have firing_step := unary_firing_step event.firing
        simpa only [event.source_eq, event.target_eq] using firing_step
    | binary event =>
        have firing_step := binary_firing_step event.firing
        simpa only [event.source_eq, event.target_eq] using firing_step
    | parL q step ih => exact .parL q ih
    | parR p step ih => exact .parR p ih
    | nu step ih => exact .nu ih
  · intro step
    induction step with
    | comm1 channel datum body => exact .unary (unaryEvent channel datum body)
    | comm2 channel first second body => exact .binary (binaryEvent channel first second body)
    | parL q step ih => exact .parL q ih
    | parR p step ih => exact .parR p ih
    | nu step ih => exact .nu ih

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredCommunication
