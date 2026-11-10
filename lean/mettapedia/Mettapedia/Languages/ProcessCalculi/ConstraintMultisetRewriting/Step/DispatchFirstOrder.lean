import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DispatchRational
import Mettapedia.Logic.LP.UnificationIdempotence

/-!
# First-order terms inside second-order frames: the first rung of the ladder

**The edge** (`firstOrderToSecond`). A first-order signature is a binding signature with one sort
whose operators bind nothing (`lpSig`). A first-order term is a second-order term over the frame
with one parameterless metavariable per variable (`lpFrame`, `encode`), and a first-order
substitution is the assignment of the encoded images. The target is the canonical second-order
instance, `Frames.contextual`: frames are arbitrary families of metavariables with parameters. The
edge reflects the equivalence (`firstOrderToSecond_reflects`).

**The license, on every store** (`firstOrderToSecond_licensed`), for a signature with infinitely
many variables. The occurs-checked unifier's answer is most general among **all second-order
solutions**, into frames whose metavariables take parameters (`eval_absorbs`):
* a second-order solution read back as a first-order substitution (`decode`), every subterm that
  is not first-order named by a variable, is a first-order solution (`decode_eval`);
* that substitution absorbs the idempotent most general unifier;
* naming the finitely many foreign subterms of the two sides injectively (`namesFor`), reading back
  is injective on them (`decode_injective`), so the second-order solution absorbs the unifier too.

So answering with `unifyTotal` gives the second-order frames' admission
(`dispatch_admits_iff_unify`): the first rung of the ladder first-order < second-order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderDispatch

open Mettapedia.Logic.LP
open Mettapedia.OSLF
open Mettapedia.OSLF.Binding.ContextualFamily (signature generator Assignment instantiate
  instantiateArgs Observation instantiate_generator observe_injective)
open Interface (Frames)
open Interface.Translation (FrameMap)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)

universe uR

variable (σ : LPSignature.{0, 0, uR, 0})

/-- **First-order terms as a binding signature**: one sort; constants and function symbols are
operators binding nothing. -/
abbrev lpSig : Binding.Signature where
  Srt := Unit
  Op _ := σ.constants ⊕ σ.functionSymbols
  arity := fun o => match o with
    | .inl _ => []
    | .inr f => List.replicate (σ.functionArity f) (([] : List Unit), ())

/-- **The first-order frame**: one parameterless metavariable of the one sort per variable. -/
abbrev lpFrame : Frames.Frame (lpSig σ) := ⟨σ.vars, fun _ => (([] : List Unit), ())⟩

variable {σ}

/-! ## First-order terms in second-order terms -/

section Encoding

variable {V : Type} {decl : V → Binding.MetaArity (lpSig σ)}

/-- The arguments of a first-order operator, from a family of second-order terms. -/
def encodeArgs : (n : ℕ) → (Fin n → Binding.Term (signature (lpSig σ) decl) [] ()) →
    Binding.Args (signature (lpSig σ) decl) (List.replicate n (([] : List Unit), ())) []
  | 0, _ => .nil
  | n + 1, ts => .cons (ts 0) (encodeArgs n fun i => ts i.succ)

/-- **Evaluation of a first-order term** among second-order terms, at a valuation of its
variables. -/
def eval (ρ : σ.vars → Binding.Term (signature (lpSig σ) decl) [] ()) :
    Term σ → Binding.Term (signature (lpSig σ) decl) [] ()
  | .var v => ρ v
  | .const c => .op (.inl (.inl c)) .nil
  | .app f ts => .op (.inl (.inr f)) (encodeArgs (σ.functionArity f) fun i => eval ρ (ts i))

theorem instantiateArgs_encodeArgs {W : Type} {decl' : W → Binding.MetaArity (lpSig σ)}
    (τ : Assignment decl decl') :
    ∀ (n : ℕ) (ts : Fin n → Binding.Term (signature (lpSig σ) decl) [] ()),
      instantiateArgs τ (encodeArgs n ts) = encodeArgs n fun i => instantiate τ (ts i)
  | 0, _ => rfl
  | n + 1, ts => by
      have rest := instantiateArgs_encodeArgs τ n fun i => ts i.succ
      simp only [encodeArgs, instantiateArgs]
      rw [rest]

/-- **Instantiation commutes with evaluation.** -/
theorem instantiate_eval {W : Type} {decl' : W → Binding.MetaArity (lpSig σ)}
    (τ : Assignment decl decl') (ρ : σ.vars → Binding.Term (signature (lpSig σ) decl) [] ()) :
    ∀ t : Term σ, instantiate τ (eval ρ t) = eval (fun v => instantiate τ (ρ v)) t
  | .var _ => rfl
  | .const _ => rfl
  | .app f ts => by
      have args := instantiateArgs_encodeArgs τ (σ.functionArity f) fun i => eval ρ (ts i)
      simp only [eval, instantiate]
      rw [args]
      exact congrArg (Binding.Term.op _)
        (congrArg (encodeArgs _) (funext fun i => instantiate_eval τ ρ (ts i)))

/-- **Evaluation after a first-order substitution** is evaluation at the evaluated images. -/
theorem eval_applyTerm (ρ : σ.vars → Binding.Term (signature (lpSig σ) decl) [] ())
    (θ : Subst σ) : ∀ t : Term σ, eval ρ (θ.applyTerm t) = eval (fun v => eval ρ (θ v)) t
  | .var _ => rfl
  | .const _ => rfl
  | .app _ ts => congrArg (Binding.Term.op _)
      (congrArg (encodeArgs _) (funext fun i => eval_applyTerm ρ θ (ts i)))

end Encoding

variable (σ) in
/-- **A first-order term as a second-order term** over the first-order frame. -/
def encode : Term σ → Binding.Term (signature (lpSig σ) (lpFrame σ).arity) [] () :=
  eval (generator (lpFrame σ).arity)

theorem instantiate_encode {W : Type} {decl' : W → Binding.MetaArity (lpSig σ)}
    (τ : Assignment (lpFrame σ).arity decl') (t : Term σ) : instantiate τ (encode σ t) = eval τ t := by
  unfold encode
  rw [instantiate_eval]
  exact congrArg (fun ρ => eval ρ t) (funext fun v => instantiate_generator τ v)

theorem encode_applyTerm (θ : Subst σ) (t : Term σ) :
    encode σ (θ.applyTerm t) = instantiate (fun v => encode σ (θ v)) (encode σ t) := by
  rw [instantiate_encode]
  exact eval_applyTerm _ θ t

variable (σ) in
/-- **First-order terms inside the second-order frames**, as a map of frame instances. -/
def firstOrderToSecond : FrameMap (Rational.finiteFrames σ) (Frames.contextual (lpSig σ)) where
  obj _ := lpFrame σ
  tm t := ⟨[], (), encode σ t⟩
  hom θ := fun v => encode σ (θ v)
  act θ t := congrArg (fun u => (⟨[], (), u⟩ : Observation (lpSig σ) (lpFrame σ).arity))
    (encode_applyTerm θ t)
  preserves same := congrArg (fun u => (⟨[], (), encode σ u⟩ : Observation (lpSig σ) (lpFrame σ).arity)) same

/-! ## Reading second-order terms back -/

section Decoding

variable {V : Type} {decl : V → Binding.MetaArity (lpSig σ)}

mutual

/-- **The foreign subterms** of a second-order term: its variables and metavariable occurrences
outside first-order operators. -/
def leaves : {Γ : Binding.Ctx (lpSig σ)} → {s : Unit} → Binding.Term (signature (lpSig σ) decl) Γ s →
    List (Observation (lpSig σ) decl)
  | Γ, s, .var x => [⟨Γ, s, .var x⟩]
  | _, _, .op (.inl (.inl _)) _ => []
  | _, _, .op (.inl (.inr _)) args => leavesArgs args
  | Γ, s, .op (.inr g) args => [⟨Γ, s, .op (.inr g) args⟩]

def leavesArgs : {as : List (List Unit × Unit)} → {Γ : Binding.Ctx (lpSig σ)} →
    Binding.Args (signature (lpSig σ) decl) as Γ → List (Observation (lpSig σ) decl)
  | _, _, .nil => []
  | _, _, .cons head tail => leaves head ++ leavesArgs tail

end

variable (e : Observation (lpSig σ) decl → σ.vars)

mutual

/-- **Reading a second-order term back as a first-order term**: first-order operators are kept,
every foreign subterm becomes the variable `e` names it by. -/
def decode : {Γ : Binding.Ctx (lpSig σ)} → {s : Unit} → Binding.Term (signature (lpSig σ) decl) Γ s →
    Term σ
  | Γ, s, .var x => .var (e ⟨Γ, s, .var x⟩)
  | _, _, .op (.inl (.inl c)) _ => .const c
  | _, _, .op (.inl (.inr f)) args =>
      .app f fun i => decodeArgs args (Fin.cast (by simp) i)
  | Γ, s, .op (.inr g) args => .var (e ⟨Γ, s, .op (.inr g) args⟩)

def decodeArgs : {as : List (List Unit × Unit)} → {Γ : Binding.Ctx (lpSig σ)} →
    Binding.Args (signature (lpSig σ) decl) as Γ → Fin as.length → Term σ
  | _, _, .nil, i => i.elim0
  | _, _, .cons head tail, i => Fin.cases (decode head) (fun j => decodeArgs tail j) i

end

theorem decodeArgs_encodeArgs : ∀ (n : ℕ) (ts : Fin n → Binding.Term (signature (lpSig σ) decl) [] ())
    (h : n = (List.replicate n (([] : List Unit), ())).length) (i : Fin n),
    decodeArgs e (encodeArgs n ts) (Fin.cast h i) = decode e (ts i)
  | 0, _, _, i => i.elim0
  | n + 1, ts, _, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact decodeArgs_encodeArgs n (fun j => ts j.succ) (by simp) j

/-- **Reading back is a homomorphism**: an evaluated first-order term reads back as the term under
the read-back valuation. -/
theorem decode_eval (ρ : σ.vars → Binding.Term (signature (lpSig σ) decl) [] ()) :
    ∀ t : Term σ, decode e (eval ρ t) = Subst.applyTerm (σ := σ) (fun v => decode e (ρ v)) t
  | .var _ => rfl
  | .const _ => rfl
  | .app f ts => by
      show Term.app f (fun i => decodeArgs e (encodeArgs _ fun i => eval ρ (ts i)) (Fin.cast _ i)) =
        Term.app f (fun i => Subst.applyTerm (σ := σ) (fun v => decode e (ρ v)) (ts i))
      congr 1
      funext i
      rw [decodeArgs_encodeArgs]
      exact decode_eval ρ (ts i)

mutual

/-- **Reading back is injective** where the naming is injective on the foreign subterms. -/
theorem decode_injective : ∀ {Γ : Binding.Ctx (lpSig σ)} {s : Unit}
    (a b : Binding.Term (signature (lpSig σ) decl) Γ s),
    (∀ ℓ ∈ leaves a ++ leaves b, ∀ ℓ' ∈ leaves a ++ leaves b, e ℓ = e ℓ' → ℓ = ℓ') →
    decode e a = decode e b → a = b
  | _, _, .var x, b, inj, same => by
      cases b with
      | var y =>
          simp only [decode, Term.var.injEq] at same
          exact observe_injective (inj _ (by simp [leaves, Binding.ContextualFamily.observe]) _
            (by simp [leaves, Binding.ContextualFamily.observe]) same)
      | op o args =>
          rcases o with (c | f) | g
          · simp [decode] at same
          · simp [decode] at same
          · simp only [decode, Term.var.injEq] at same
            exact observe_injective (inj _ (by simp [leaves, Binding.ContextualFamily.observe]) _
            (by simp [leaves, Binding.ContextualFamily.observe]) same)
  | _, _, .op (.inr g) args, b, inj, same => by
      cases b with
      | var y =>
          simp only [decode, Term.var.injEq] at same
          exact observe_injective (inj _ (by simp [leaves, Binding.ContextualFamily.observe]) _
            (by simp [leaves, Binding.ContextualFamily.observe]) same)
      | op o args' =>
          rcases o with (c | f) | g'
          · simp [decode] at same
          · simp [decode] at same
          · simp only [decode, Term.var.injEq] at same
            exact observe_injective (inj _ (by simp [leaves, Binding.ContextualFamily.observe]) _
            (by simp [leaves, Binding.ContextualFamily.observe]) same)
  | _, _, .op (.inl (.inl c)) args, b, _, same => by
      cases b with
      | var y => simp [decode] at same
      | op o args' =>
          rcases o with (c' | f) | g
          · simp only [decode, Term.const.injEq] at same
            subst same
            cases args
            cases args'
            rfl
          · simp [decode] at same
          · simp [decode] at same
  | _, _, .op (.inl (.inr f)) args, b, inj, same => by
      cases b with
      | var y => simp [decode] at same
      | op o args' =>
          rcases o with (c | f') | g
          · simp [decode] at same
          · simp only [decode, Term.app.injEq] at same
            obtain ⟨rfl, kids⟩ := same
            have pointwise := congrFun (eq_of_heq kids)
            have equal := decodeArgs_injective args args' (fun ℓ hℓ ℓ' hℓ' => inj ℓ
              (by simpa [leaves] using hℓ) ℓ' (by simpa [leaves] using hℓ')) fun i => by
                have := pointwise (Fin.cast (by simp) i)
                simpa using this
            rw [equal]
          · simp [decode] at same

theorem decodeArgs_injective : ∀ {as : List (List Unit × Unit)} {Γ : Binding.Ctx (lpSig σ)}
    (a b : Binding.Args (signature (lpSig σ) decl) as Γ),
    (∀ ℓ ∈ leavesArgs a ++ leavesArgs b, ∀ ℓ' ∈ leavesArgs a ++ leavesArgs b, e ℓ = e ℓ' → ℓ = ℓ') →
    (∀ i, decodeArgs e a i = decodeArgs e b i) → a = b
  | _, _, .nil, .nil, _, _ => rfl
  | _, _, .cons head tail, .cons head' tail', inj, same => by
      have first := decode_injective head head'
        (fun ℓ hℓ ℓ' hℓ' => inj ℓ (by simp only [leavesArgs, List.mem_append] at hℓ ⊢; tauto) ℓ'
          (by simp only [leavesArgs, List.mem_append] at hℓ' ⊢; tauto)) (same 0)
      have rest := decodeArgs_injective tail tail'
        (fun ℓ hℓ ℓ' hℓ' => inj ℓ (by simp only [leavesArgs, List.mem_append] at hℓ ⊢; tauto) ℓ'
          (by simp only [leavesArgs, List.mem_append] at hℓ' ⊢; tauto)) fun j => same j.succ
      rw [first, rest]

end

end Decoding

/-! ## The license -/

section License

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [Infinite σ.vars]

variable {V : Type} {decl : V → Binding.MetaArity (lpSig σ)}

/-- **Names for a list of foreign subterms**, injective on the list. -/
noncomputable def namesFor (L : List (Observation (lpSig σ) decl)) : Observation (lpSig σ) decl → σ.vars := by
  classical
  exact fun ℓ => Infinite.natEmbedding σ.vars (L.idxOf ℓ)

omit [DecidableEq σ.vars] in
theorem namesFor_injOn (L : List (Observation (lpSig σ) decl)) :
    ∀ ℓ ∈ L, ∀ ℓ' ∈ L, namesFor L ℓ = namesFor L ℓ' → ℓ = ℓ' := by
  classical
  intro ℓ member ℓ' _ same
  unfold namesFor at same
  exact (List.idxOf_inj member).mp ((Infinite.natEmbedding σ.vars).injective same)

/-- **The unifier's answer is most general among second-order solutions**: a second-order solution
of a first-order store absorbs it. -/
theorem eval_absorbs {K : EquationStore (Term σ)} {θ : Subst σ} (accepted : unifyTotal K = some θ)
    (τ : σ.vars → Binding.Term (signature (lpSig σ) decl) [] ())
    (solves : ∀ e ∈ K, eval τ e.1 = eval τ e.2) (v : σ.vars) : eval τ (θ v) = τ v := by
  let L := leaves (eval τ (θ v)) ++ leaves (τ v)
  have unifies : Unifies (fun w => decode (namesFor L) (τ w)) K := by
    intro e member
    rw [← decode_eval, ← decode_eval, solves e member]
  have absorbs := Subst.absorbs_of_moreGeneral
    (unifyTotal_relevantIdempotent K θ accepted).absorbs (unifyTotal_mgu K θ accepted _ unifies) v
  rw [← decode_eval] at absorbs
  exact decode_injective (namesFor L) _ _ (namesFor_injOn L) absorbs

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [Infinite σ.vars] in
/-- A second-order solution of a first-order store makes it first-order solvable: read it back. -/
theorem consistent_of_secondOrder {K : EquationStore (Term σ)}
    (τ : σ.vars → Binding.Term (signature (lpSig σ) decl) [] ()) (e₀ : Observation (lpSig σ) decl → σ.vars)
    (solves : ∀ e ∈ K, eval τ e.1 = eval τ e.2) : (FirstOrder.action σ).Consistent K := by
  refine ⟨fun w => decode e₀ (τ w), fun e member => ?_⟩
  show Subst.applyTerm (σ := σ) (fun w => decode e₀ (τ w)) e.1 =
    Subst.applyTerm (σ := σ) (fun w => decode e₀ (τ w)) e.2
  rw [← decode_eval, ← decode_eval, solves e member]

/-- **Every second-order solution of a first-order store absorbs the unifier's answer.** -/
theorem secondOrder_absorbs (K : EquationStore (Term σ)) (τ : Assignment (lpFrame σ).arity decl)
    (solved : ∀ e ∈ K, instantiate τ (encode σ e.1) = instantiate τ (encode σ e.2)) :
    ∃ θ : Subst σ, unifyTotal K = some θ ∧ (fun v => instantiate τ (encode σ (θ v))) = τ := by
  have solves : ∀ e ∈ K, eval τ e.1 = eval τ e.2 := by
    intro e member
    have equated := solved e member
    rwa [instantiate_encode, instantiate_encode] at equated
  obtain ⟨θ, accepted⟩ := (FirstOrder.accepted_iff_consistent K).mpr
    (consistent_of_secondOrder τ (namesFor []) solves)
  exact ⟨θ, accepted, funext fun v => (instantiate_encode τ (θ v)).trans (eval_absorbs accepted τ solves v)⟩

/-- **Covering on every store.** -/
theorem firstOrderToSecond_coversAt (K : EquationStore (Term σ)) :
    (firstOrderToSecond σ).CoversAt (a := PUnit.unit) K := by
  intro G τ solved
  obtain ⟨θ, accepted, composite⟩ := secondOrder_absorbs (decl := G.arity) K τ
    fun e member => observe_injective (solved _ (List.mem_map.mpr ⟨e, member, rfl⟩))
  refine ⟨PUnit.unit, θ, τ, (FirstOrder.accepted_principal K θ accepted).sound, fun t => ?_⟩
  exact congrArg (fun α : Assignment (lpFrame σ).arity G.arity =>
    (⟨[], (), instantiate α (encode σ t)⟩ : Observation (lpSig σ) G.arity)) composite.symm

/-- **The first-order edge is licensed on every store.** -/
theorem firstOrderToSecond_licensed : (firstOrderToSecond σ).Licensed :=
  fun _ K => (firstOrderToSecond_coversAt K).licensedAt

/-- The encoded variables. -/
def generators (v : σ.vars) : Observation (lpSig σ) (lpFrame σ).arity :=
  ⟨[], (), generator (lpFrame σ).arity v⟩

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [Infinite σ.vars] in
theorem generators_injective : Function.Injective (generators (σ := σ)) := by
  intro v w same
  have terms := observe_injective same
  simp only [generator, Binding.Term.op.injEq, Sum.inr.injEq] at terms
  obtain ⟨operators, -⟩ := terms
  exact congrArg Binding.ContextualFamily.Operator.key operators

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
/-- **The edge reflects the equivalence**: encoding is injective. -/
theorem firstOrderToSecond_reflects : (firstOrderToSecond σ).Reflects := by
  intro _ s t same
  have encoded : encode σ s = encode σ t := observe_injective same
  have back := congrArg (decode (Function.invFun (generators (σ := σ)))) encoded
  unfold encode at back
  rw [decode_eval, decode_eval] at back
  have identity : (fun v => decode (Function.invFun (generators (σ := σ)))
      (generator (lpFrame σ).arity v)) = Subst.id σ :=
    funext fun v => congrArg Term.var (Function.leftInverse_invFun generators_injective v)
  rw [identity, Subst.applyTerm_id, Subst.applyTerm_id] at back
  exact back

/-! ## Dispatch to the occurs-checked unifier -/

/-- **The second-order frames dispatch to `unifyTotal`.** For any step over the second-order frames,
at a firing dispatched along the first-order edge, admission is the shapes, the enabling, and the
guards at the unifier's answer; a refusal of the unifier refuses the firing. -/
theorem dispatch_admits_iff_unify {O : Type} [DecidableEq O] {State : Type} {Firing : State → Type}
    (P : Interface.Step (Frames.contextual (lpSig σ)) O State Firing) [P.Guarded]
    {s : State} {f : Firing s}
    (d : (firstOrderToSecond σ).Dispatched P f) :
    P.Admits f ↔ P.Shapes f ∧
      Enabled (fun _ : O => ()) (P.present s) ((P.selection f).commit (T := Unit)) ∧
      (Rational.unifyDecider (a := d.source) d.problem).Accepts d.guards :=
  FrameMap.dispatch_admits_iff_decider firstOrderToSecond_reflects Rational.unifyDecider P d
    (firstOrderToSecond_licensed _ _)

end License

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderDispatch

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

#print axioms FirstOrderDispatch.firstOrderToSecond
#print axioms FirstOrderDispatch.instantiate_eval
#print axioms FirstOrderDispatch.encode_applyTerm
#print axioms FirstOrderDispatch.decode_eval
#print axioms FirstOrderDispatch.decode_injective
#print axioms FirstOrderDispatch.eval_absorbs
#print axioms FirstOrderDispatch.firstOrderToSecond_coversAt
#print axioms FirstOrderDispatch.firstOrderToSecond_licensed
#print axioms FirstOrderDispatch.firstOrderToSecond_reflects
#print axioms FirstOrderDispatch.dispatch_admits_iff_unify

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
