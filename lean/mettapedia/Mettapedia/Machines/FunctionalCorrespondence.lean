import Mathlib.Logic.Relation

/-!
# The functional correspondence: interpreters and their abstract machines

The functional-correspondence method derives an abstract machine from an
evaluator (interpreter → CPS → defunctionalize → machine), so a different
evaluation semantics yields a different machine. This file formalizes two
endpoint evaluator/machine pairs on one shared term language and proves their
forward correspondence. It does not yet mechanize the CPS and
defunctionalization transformations themselves:

* call-by-value evaluator ⟶ **CEK-shaped machine** (`CEK`): frames hold the
  pending argument and then the evaluated operator — the eager control core;
* call-by-name evaluator ⟶ **Krivine-shaped machine** (`Krivine`): the stack
  holds unevaluated thunks — the demand-driven control core (call-by-need is
  this machine plus a memoizing heap, developed separately).

Both machines run the *same* `Tm` (the shared substrate); only the control
structure differs. For each we prove the correspondence theorem: whenever
the fueled evaluator produces a value, the machine, started on any
continuation/stack, reaches the matching return configuration — by induction
on fuel, uniformly in the continuation. Together with machine determinism
(`CEK.steps_final_unique`) the evaluator answer is *the* machine answer.

No project-specific axioms are introduced; evaluators are total fueled
functions, machines are total step functions, and all runs are witnessed step
chains.
-/

namespace Mettapedia.Machines

/-- The shared term substrate: de Bruijn λ-terms with literals. -/
inductive Tm : Type
  | var : Nat → Tm
  | lam : Tm → Tm
  | app : Tm → Tm → Tm
  | lit : Nat → Tm
deriving Repr, DecidableEq

/-! ## Call-by-value: evaluator and CEK machine -/

namespace CEK

/-- CBV values: literals and closures over CBV environments. -/
inductive Val : Type
  | lit : Nat → Val
  | clo : Tm → List Val → Val

abbrev Env := List Val

/-- The fueled call-by-value reference evaluator (left-to-right). -/
def evalV : Nat → Env → Tm → Option Val
  | 0, _, _ => none
  | _ + 1, ρ, .var i => ρ[i]?
  | _ + 1, _, .lit k => some (.lit k)
  | _ + 1, ρ, .lam b => some (.clo b ρ)
  | n + 1, ρ, .app f a =>
    match evalV n ρ f with
    | none => none
    | some fv =>
      match evalV n ρ a with
      | none => none
      | some av =>
        match fv with
        | .lit _ => none
        | .clo b ρ' => evalV n (av :: ρ') b

/-- Defunctionalized continuations: evaluate the argument next, then call. -/
inductive Frame : Type
  | argOf : Tm → Env → Frame
  | callWith : Val → Frame

abbrev Kont := List Frame

/-- Machine control: evaluating a term, or returning a value. -/
inductive Ctl : Type
  | ev : Tm → Env → Ctl
  | ret : Val → Ctl

/-- CEK machine states. -/
structure St where
  ctl : Ctl
  k : Kont

/-- The CEK transition function (`none` = final or stuck). -/
def step : St → Option St
  | ⟨.ev (.var i) ρ, k⟩ => (ρ[i]?).map fun v => ⟨.ret v, k⟩
  | ⟨.ev (.lit m) _, k⟩ => some ⟨.ret (.lit m), k⟩
  | ⟨.ev (.lam b) ρ, k⟩ => some ⟨.ret (.clo b ρ), k⟩
  | ⟨.ev (.app f a) ρ, k⟩ => some ⟨.ev f ρ, .argOf a ρ :: k⟩
  | ⟨.ret v, .argOf a ρ :: k⟩ => some ⟨.ev a ρ, .callWith v :: k⟩
  | ⟨.ret v, .callWith (.clo b ρ') :: k⟩ => some ⟨.ev b (v :: ρ'), k⟩
  | ⟨.ret _, .callWith (.lit _) :: _⟩ => none
  | ⟨.ret _, []⟩ => none

/-- One machine step as a relation. -/
abbrev StepRel (s s' : St) : Prop := step s = some s'

/-- Zero or more machine steps. -/
abbrev Steps : St → St → Prop := Relation.ReflTransGen StepRel

/-- **Functional correspondence, CBV/CEK.** If the evaluator returns `v`,
the machine walks from evaluating the term to returning `v`, uniformly in
the surrounding continuation. -/
theorem eval_to_machine :
    ∀ (n : Nat) (ρ : Env) (t : Tm) (v : Val),
      evalV n ρ t = some v → ∀ k : Kont, Steps ⟨.ev t ρ, k⟩ ⟨.ret v, k⟩ := by
  intro n
  induction n with
  | zero =>
    intro ρ t v h
    have h' : (none : Option Val) = some v := h
    simp at h'
  | succ n ih =>
    intro ρ t v h k
    cases t with
    | var i =>
      simp only [evalV] at h
      refine Relation.ReflTransGen.single ?_
      show (ρ[i]?).map (fun v => ({ ctl := .ret v, k := k } : St)) = some ⟨.ret v, k⟩
      rw [h]
      exact rfl
    | lit m =>
      simp only [evalV, Option.some.injEq] at h
      subst h
      exact Relation.ReflTransGen.single rfl
    | lam b =>
      simp only [evalV, Option.some.injEq] at h
      subst h
      exact Relation.ReflTransGen.single rfl
    | app f a =>
      simp only [evalV] at h
      cases hf : evalV n ρ f with
      | none =>
        rw [hf] at h
        exact absurd (show (none : Option Val) = some v from h).symm (Option.some_ne_none v)
      | some fv =>
        rw [hf] at h
        cases ha : evalV n ρ a with
        | none =>
          rw [ha] at h
          exact absurd (show (none : Option Val) = some v from h).symm (Option.some_ne_none v)
        | some av =>
          rw [ha] at h
          cases fv with
          | lit m =>
            exact absurd (show (none : Option Val) = some v from h).symm (Option.some_ne_none v)
          | clo b ρ' =>
            have hb : evalV n (av :: ρ') b = some v := h
            have s1 : StepRel ⟨.ev (.app f a) ρ, k⟩ ⟨.ev f ρ, .argOf a ρ :: k⟩ := rfl
            have wf : Steps ⟨.ev f ρ, .argOf a ρ :: k⟩ ⟨.ret (.clo b ρ'), .argOf a ρ :: k⟩ :=
              ih ρ f (.clo b ρ') hf (.argOf a ρ :: k)
            have s2 : StepRel ⟨.ret (.clo b ρ'), .argOf a ρ :: k⟩
                ⟨.ev a ρ, .callWith (.clo b ρ') :: k⟩ := rfl
            have wa : Steps ⟨.ev a ρ, .callWith (.clo b ρ') :: k⟩
                ⟨.ret av, .callWith (.clo b ρ') :: k⟩ :=
              ih ρ a av ha (.callWith (.clo b ρ') :: k)
            have s3 : StepRel ⟨.ret av, .callWith (.clo b ρ') :: k⟩
                ⟨.ev b (av :: ρ'), k⟩ := rfl
            have wb : Steps ⟨.ev b (av :: ρ'), k⟩ ⟨.ret v, k⟩ :=
              ih (av :: ρ') b v hb k
            exact .head s1 (wf.trans (.head s2 (wa.trans (.head s3 wb))))

/-- A final state: the machine has no move. -/
def Final (s : St) : Prop := step s = none

theorem final_ret_nil (v : Val) : Final ⟨.ret v, []⟩ := rfl

/-- The machine is a function, so runs to final states are unique: the
evaluator's answer is *the* machine's answer. -/
theorem steps_final_unique {s f₁ f₂ : St}
    (h₁ : Steps s f₁) (h₂ : Steps s f₂)
    (hf₁ : Final f₁) (hf₂ : Final f₂) : f₁ = f₂ := by
  revert h₂
  induction h₁ using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro h₂
    rcases Relation.ReflTransGen.cases_head h₂ with h | ⟨c, hc, _⟩
    · exact h
    · rw [Final] at hf₁
      rw [StepRel, hf₁] at hc
      exact absurd hc.symm (Option.some_ne_none c)
  | head hab _ ih =>
    intro h₂
    rcases Relation.ReflTransGen.cases_head h₂ with h | ⟨c, hc, h₂'⟩
    · subst h
      rw [Final] at hf₂
      rw [StepRel, hf₂] at hab
      exact absurd hab.symm (Option.some_ne_none _)
    · rw [StepRel] at hab hc
      rw [hab] at hc
      cases hc
      exact ih h₂'

end CEK

/-! ## Call-by-name: evaluator and Krivine machine -/

namespace Krivine

/-- A thunk: an unevaluated term closed over a thunk environment. -/
inductive NThunk : Type
  | mk : Tm → List NThunk → NThunk

abbrev NEnv := List NThunk

/-- Weak-head values for call-by-name. -/
inductive NVal : Type
  | lit : Nat → NVal
  | clo : Tm → NEnv → NVal

/-- The fueled call-by-name reference evaluator (to weak head normal form).
Variables force their thunk; arguments are *not* evaluated at calls. -/
def evalN : Nat → NEnv → Tm → Option NVal
  | 0, _, _ => none
  | n + 1, ρ, .var i =>
    match ρ[i]? with
    | none => none
    | some (.mk t ρ') => evalN n ρ' t
  | _ + 1, _, .lit k => some (.lit k)
  | _ + 1, ρ, .lam b => some (.clo b ρ)
  | n + 1, ρ, .app f a =>
    match evalN n ρ f with
    | none => none
    | some (.lit _) => none
    | some (.clo b ρ') => evalN n (NThunk.mk a ρ :: ρ') b

/-- Krivine machine states: control term, thunk environment, thunk stack. -/
structure KSt where
  t : Tm
  ρ : NEnv
  s : List NThunk

/-- The Krivine transition function: push unevaluated arguments, pop into
binders, jump through variables. `none` = weak-head final (or stuck). -/
def kstep : KSt → Option KSt
  | ⟨.var i, ρ, s⟩ =>
    (ρ[i]?).map fun th => match th with | .mk t ρ' => ⟨t, ρ', s⟩
  | ⟨.app f a, ρ, s⟩ => some ⟨f, ρ, .mk a ρ :: s⟩
  | ⟨.lam b, ρ, th :: s⟩ => some ⟨b, th :: ρ, s⟩
  | ⟨.lam _, _, []⟩ => none
  | ⟨.lit _, _, _⟩ => none

abbrev KStepRel (s s' : KSt) : Prop := kstep s = some s'
abbrev KSteps : KSt → KSt → Prop := Relation.ReflTransGen KStepRel

/-- The machine configuration that presents a weak-head value over stack
`s`. A closure pins its environment; a literal's resting environment is
existential (it is whatever environment the walk ended in). -/
def Presents (w : NVal) (s : List NThunk) (st : KSt) : Prop :=
  match w with
  | .clo b ρw => st = ⟨.lam b, ρw, s⟩
  | .lit k => ∃ ρ', st = ⟨.lit k, ρ', s⟩

/-- **Functional correspondence, CBN/Krivine.** If the evaluator produces a
weak-head value, the machine, started with any pending argument stack,
reaches a configuration presenting that value over the same stack. -/
theorem eval_to_machine :
    ∀ (n : Nat) (ρ : NEnv) (t : Tm) (w : NVal),
      evalN n ρ t = some w →
      ∀ s : List NThunk, ∃ st, KSteps ⟨t, ρ, s⟩ st ∧ Presents w s st := by
  intro n
  induction n with
  | zero =>
    intro ρ t w h
    have h' : (none : Option NVal) = some w := h
    simp at h'
  | succ n ih =>
    intro ρ t w h s
    cases t with
    | var i =>
      simp only [evalN] at h
      cases hl : ρ[i]? with
      | none =>
        rw [hl] at h
        exact absurd (show (none : Option NVal) = some w from h).symm (Option.some_ne_none w)
      | some th =>
        rw [hl] at h
        cases th with
        | mk t' ρ' =>
          have h' : evalN n ρ' t' = some w := h
          obtain ⟨st, hrun, hpres⟩ := ih ρ' t' w h' s
          have s1 : KStepRel ⟨.var i, ρ, s⟩ ⟨t', ρ', s⟩ := by
            show (ρ[i]?).map (fun th => match th with | .mk t ρ'' => ({ t := t, ρ := ρ'', s := s } : KSt)) = some ⟨t', ρ', s⟩
            rw [hl]
            exact rfl
          exact ⟨st, .head s1 hrun, hpres⟩
    | lit k =>
      simp only [evalN, Option.some.injEq] at h
      subst h
      exact ⟨⟨.lit k, ρ, s⟩, .refl, ⟨ρ, rfl⟩⟩
    | lam b =>
      simp only [evalN, Option.some.injEq] at h
      subst h
      exact ⟨⟨.lam b, ρ, s⟩, .refl, rfl⟩
    | app f a =>
      simp only [evalN] at h
      cases hf : evalN n ρ f with
      | none =>
        rw [hf] at h
        exact absurd (show (none : Option NVal) = some w from h).symm (Option.some_ne_none w)
      | some fw =>
        rw [hf] at h
        cases fw with
        | lit m =>
          exact absurd (show (none : Option NVal) = some w from h).symm (Option.some_ne_none w)
        | clo b ρ' =>
          have hb : evalN n (NThunk.mk a ρ :: ρ') b = some w := h
          have s1 : KStepRel ⟨.app f a, ρ, s⟩ ⟨f, ρ, .mk a ρ :: s⟩ := rfl
          obtain ⟨stf, hrunf, hpresf⟩ := ih ρ f (.clo b ρ') hf (.mk a ρ :: s)
          -- a closure presentation pins the machine configuration exactly
          have hstf : stf = ⟨.lam b, ρ', .mk a ρ :: s⟩ := hpresf
          subst hstf
          have s2 : KStepRel ⟨.lam b, ρ', .mk a ρ :: s⟩ ⟨b, .mk a ρ :: ρ', s⟩ := rfl
          obtain ⟨st, hrun, hpres⟩ := ih (NThunk.mk a ρ :: ρ') b w hb s
          exact ⟨st, .head s1 (hrunf.trans (.head s2 hrun)), hpres⟩

end Krivine

end Mettapedia.Machines
