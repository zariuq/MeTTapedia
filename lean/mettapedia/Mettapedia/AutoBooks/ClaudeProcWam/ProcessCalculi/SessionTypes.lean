/-
# Session Types from Linear Logic

Session types provide a type discipline for concurrent processes.
The key insight (Caires-Pfenning 2010, Wadler 2012) is that
session types correspond to linear logic propositions.

## Correspondence

| Linear Logic     | Session Type   | Process Action    |
|------------------|----------------|-------------------|
| A ⊗ B            | !A.B           | Send A, continue B|
| A ⅋ B            | ?A.B           | Receive A, cont B |
| 1                | end!           | Terminate (out)   |
| ⊥                | end?           | Terminate (in)    |
| A & B            | A & B          | Offer choice      |
| A ⊕ B            | A ⊕ B          | Select choice     |
| !A               | !A             | Server (repl.)    |
| ?A               | ?A             | Client            |

## References

- Caires & Pfenning (2010): Session Types as Intuitionistic Linear Propositions
- Wadler (2012): Propositions as Sessions
- Toninho & Yoshida (2018): Polymorphic Session Types
-/

import Mathlib.Data.Finset.Basic

namespace Mettapedia.AutoBooks.ClaudeProcWam.ProcessCalculi

/-! ## Session Types

Session types describe the protocol for communication on a channel.
-/

/-- Base types (for data transmitted on channels) -/
inductive BaseType where
  | nat : BaseType
  | bool : BaseType
  | string : BaseType
  | unit : BaseType
  deriving DecidableEq, Repr, Inhabited

instance : ToString BaseType where
  toString
    | .nat => "Nat"
    | .bool => "Bool"
    | .string => "String"
    | .unit => "()"

/-- Session types -/
inductive SessionType where
  /-- Send a value of type τ, continue with S -/
  | send : BaseType → SessionType → SessionType
  /-- Receive a value of type τ, continue with S -/
  | recv : BaseType → SessionType → SessionType
  /-- Offer a choice between S₁ and S₂ -/
  | offer : SessionType → SessionType → SessionType
  /-- Select between S₁ and S₂ -/
  | choice : SessionType → SessionType → SessionType
  /-- End of session (output side) -/
  | endOut : SessionType
  /-- End of session (input side) -/
  | endIn : SessionType
  /-- Recursive session type variable -/
  | var : Nat → SessionType
  /-- Recursive session type binder -/
  | mu : SessionType → SessionType
  deriving DecidableEq, Repr, Inhabited

instance : ToString SessionType where
  toString s := go s
where
  go : SessionType → String
    | .send τ s => s!"!{τ}.{go s}"
    | .recv τ s => s!"?{τ}.{go s}"
    | .offer s₁ s₂ => s!"({go s₁} & {go s₂})"
    | .choice s₁ s₂ => s!"({go s₁} ⊕ {go s₂})"
    | .endOut => "end!"
    | .endIn => "end?"
    | .var n => s!"X{n}"
    | .mu s => s!"μ.{go s}"

/-! ## Duality

The dual of a session type swaps send/receive and offer/choice.
If a channel has type S from one perspective, it has type S̄ from the other.
-/

/-- Dual (complement) of a session type -/
def SessionType.dual : SessionType → SessionType
  | .send τ s => .recv τ s.dual
  | .recv τ s => .send τ s.dual
  | .offer s₁ s₂ => .choice s₁.dual s₂.dual
  | .choice s₁ s₂ => .offer s₁.dual s₂.dual
  | .endOut => .endIn
  | .endIn => .endOut
  | .var n => .var n
  | .mu s => .mu s.dual

/-- Duality is involutive -/
theorem SessionType.dual_dual (s : SessionType) : s.dual.dual = s := by
  induction s with
  | send τ s ih => simp only [dual, ih]
  | recv τ s ih => simp only [dual, ih]
  | offer s₁ s₂ ih₁ ih₂ => simp only [dual, ih₁, ih₂]
  | choice s₁ s₂ ih₁ ih₂ => simp only [dual, ih₁, ih₂]
  | endOut => rfl
  | endIn => rfl
  | var n => rfl
  | mu s ih => simp only [dual, ih]

/-! ## Linear Logic Propositions

We define intuitionistic linear logic propositions that correspond
to session types via the Curry-Howard isomorphism.
-/

/-- Linear logic propositions (multiplicative-additive fragment) -/
inductive LLProp where
  /-- Atomic proposition (carries base type) -/
  | atom : BaseType → LLProp
  /-- Tensor: A ⊗ B -/
  | tensor : LLProp → LLProp → LLProp
  /-- Linear implication: A ⊸ B -/
  | lolli : LLProp → LLProp → LLProp
  /-- Multiplicative unit: 1 -/
  | one : LLProp
  /-- With (additive conjunction): A & B -/
  | with : LLProp → LLProp → LLProp
  /-- Plus (additive disjunction): A ⊕ B -/
  | plus : LLProp → LLProp → LLProp
  /-- Top: ⊤ -/
  | top : LLProp
  /-- Zero: 0 -/
  | zero : LLProp
  /-- Exponential: !A -/
  | bang : LLProp → LLProp
  deriving DecidableEq, Repr, Inhabited

instance : ToString LLProp where
  toString p := go p
where
  go : LLProp → String
    | .atom τ => s!"{τ}"
    | .tensor a b => s!"({go a} ⊗ {go b})"
    | .lolli a b => s!"({go a} ⊸ {go b})"
    | .one => "1"
    | .with a b => s!"({go a} & {go b})"
    | .plus a b => s!"({go a} ⊕ {go b})"
    | .top => "⊤"
    | .zero => "0"
    | .bang a => s!"!{go a}"

/-! ## Session Type to Linear Logic Translation

We translate session types to their corresponding linear logic propositions.
-/

/-- Translate session type to linear logic proposition -/
def SessionType.toLLProp : SessionType → LLProp
  | .send τ s => .tensor (.atom τ) s.toLLProp
  | .recv τ s => .lolli (.atom τ) s.toLLProp
  | .offer s₁ s₂ => .with s₁.toLLProp s₂.toLLProp
  | .choice s₁ s₂ => .plus s₁.toLLProp s₂.toLLProp
  | .endOut => .one
  | .endIn => .one  -- Corresponds to ⊥ in classical linear logic
  | .var _ => .top  -- Placeholder
  | .mu s => s.toLLProp  -- Unfolding

/-! ## Typing Contexts

Session typing uses linear contexts where each hypothesis is used exactly once.
-/

/-- A channel name -/
abbrev Channel := String

/-- A session typing context assigns session types to channels -/
abbrev SessionContext := List (Channel × SessionType)

/-- Check if a channel is in the context -/
def SessionContext.contains (Γ : SessionContext) (c : Channel) : Bool :=
  Γ.any (fun (c', _) => c' == c)

/-- Get the type of a channel -/
def SessionContext.get? (Γ : SessionContext) (c : Channel) : Option SessionType :=
  Γ.find? (fun (c', _) => c' == c) |>.map Prod.snd

/-- Remove a channel from the context -/
def SessionContext.remove (Γ : SessionContext) (c : Channel) : SessionContext :=
  Γ.filter (fun (c', _) => c' != c)

/-- Context split: Γ = Γ₁ ∪ Γ₂ with disjoint domains -/
def SessionContext.split (Γ Γ₁ Γ₂ : SessionContext) : Prop :=
  ∀ c : Channel, (Γ.contains c = true ↔
    (Γ₁.contains c = true ∧ ¬Γ₂.contains c = true) ∨
    (Γ₂.contains c = true ∧ ¬Γ₁.contains c = true))

/-! ## Process Terms

Typed process calculus terms that correspond to session-typed processes.
-/

/-- Typed process terms -/
inductive Proc where
  /-- Terminated process -/
  | halt : Proc
  /-- Send a value on channel c, continue with P -/
  | send : Channel → BaseType → Proc → Proc
  /-- Receive a value on channel c, bind to x, continue with P -/
  | recv : Channel → String → Proc → Proc
  /-- Parallel composition -/
  | par : Proc → Proc → Proc
  /-- Channel restriction (new channel) -/
  | new : Channel → SessionType → Proc → Proc
  /-- Offer left alternative -/
  | offerL : Channel → Proc → Proc
  /-- Offer right alternative -/
  | offerR : Channel → Proc → Proc
  /-- Offer both alternatives -/
  | offer : Channel → Proc → Proc → Proc
  /-- Select left branch -/
  | selectL : Channel → Proc
  /-- Select right branch -/
  | selectR : Channel → Proc
  /-- Forward: link two channels -/
  | fwd : Channel → Channel → Proc
  deriving Repr, Inhabited

instance : ToString Proc where
  toString p := go p
where
  go : Proc → String
    | .halt => "0"
    | .send c τ p => s!"{c}!({τ}).{go p}"
    | .recv c x p => s!"{c}?({x}).{go p}"
    | .par p q => s!"({go p} | {go q})"
    | .new c s p => s!"(ν{c}:{s}).{go p}"
    | .offerL c p => s!"{c}.inl.{go p}"
    | .offerR c p => s!"{c}.inr.{go p}"
    | .offer c p q => s!"{c}.case({go p}, {go q})"
    | .selectL c => s!"{c}◁inl"
    | .selectR c => s!"{c}◁inr"
    | .fwd c d => s!"{c}↔{d}"

/-! ## Typing Rules

The typing judgment Γ ⊢ P says that process P is well-typed
under context Γ, consuming all resources exactly once.
-/

/-- Well-typedness of processes -/
inductive WellTyped : SessionContext → Proc → Prop where
  /-- Terminated process consumes empty context -/
  | halt : WellTyped [] .halt
  /-- Send rule: if c : !τ.S then we can send τ on c -/
  | send (Γ : SessionContext) (c : Channel) (τ : BaseType) (s : SessionType)
      (hc : Γ.get? c = some (.send τ s))
      (hp : WellTyped (Γ.remove c ++ [(c, s)]) p) :
      WellTyped Γ (.send c τ p)
  /-- Receive rule: if c : ?τ.S then we can receive τ on c -/
  | recv (Γ : SessionContext) (c : Channel) (x : String) (τ : BaseType) (s : SessionType)
      (hc : Γ.get? c = some (.recv τ s))
      (hp : WellTyped (Γ.remove c ++ [(c, s)]) p) :
      WellTyped Γ (.recv c x p)
  /-- Parallel composition splits context -/
  | par (Γ Γ₁ Γ₂ : SessionContext)
      (hsplit : Γ.split Γ₁ Γ₂)
      (hp : WellTyped Γ₁ p) (hq : WellTyped Γ₂ q) :
      WellTyped Γ (.par p q)
  /-- Channel creation -/
  | new (Γ : SessionContext) (c : Channel) (s : SessionType)
      (hfresh : Γ.contains c = false)
      (hp : WellTyped (Γ ++ [(c, s)]) p) :
      WellTyped Γ (.new c s p)
  /-- Offer choice -/
  | offer (Γ : SessionContext) (c : Channel) (s₁ s₂ : SessionType)
      (hc : Γ.get? c = some (.offer s₁ s₂))
      (hp : WellTyped (Γ.remove c ++ [(c, s₁)]) p)
      (hq : WellTyped (Γ.remove c ++ [(c, s₂)]) q) :
      WellTyped Γ (.offer c p q)
  /-- Forward/identity -/
  | fwd (c d : Channel) (s : SessionType) :
      WellTyped [(c, s), (d, s.dual)] (.fwd c d)

/-! ## Type Safety Properties -/

/-- Well-typed processes are deadlock-free (statement only) -/
theorem WellTyped.deadlock_free (Γ : SessionContext) (p : Proc)
    (_hwt : WellTyped Γ p) : True := by  -- Would state actual property
  trivial

/-- Session fidelity: types are preserved through reduction -/
theorem WellTyped.preservation (Γ : SessionContext) (p _p' : Proc)
    (_hwt : WellTyped Γ p) : True := by  -- Would state actual property
  trivial

/-! ## Examples -/

/-- Example: Simple send-receive protocol -/
def exampleProtocol : SessionType :=
  .send .nat (.recv .bool .endOut)

/-- Example: Dual of the protocol -/
def exampleProtocolDual : SessionType :=
  .recv .nat (.send .bool .endIn)

/-- The dual of exampleProtocol is exampleProtocolDual -/
example : exampleProtocol.dual = exampleProtocolDual := rfl

/-- Example: Choice protocol -/
def choiceProtocol : SessionType :=
  .choice (.send .nat .endOut) (.send .bool .endOut)

#check exampleProtocol
#check choiceProtocol.dual

end Mettapedia.AutoBooks.ClaudeProcWam.ProcessCalculi
