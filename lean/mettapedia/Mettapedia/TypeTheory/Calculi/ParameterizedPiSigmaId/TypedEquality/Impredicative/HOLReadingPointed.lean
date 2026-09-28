import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.HOLReadingCompile
import Mettapedia.Logic.HOL.ImpredicativeProofModulo

/-!
# Compiling HOL proofs with equality through a reading

The proofs of `HOL.ProofSyntax` (all 29 rules) are compiled through a reading
by `HOLReading.compileP`. Hypotheses, implication and the universal quantifier
compile as for proofs modulo conversion (`HOLReading.compile`); the twelve
equality rules request operations of an algebra.

**The algebra.** `EqualityRaw` is the computational part of an equality-proof
algebra: point-free reflexivity (as in the legacy algebra), symmetry,
transitivity, propositional extensionality, the forward direction of an
equation between propositions, congruence in the function and in the argument,
and function extensionality. Each operation receives the HOL types and the
native endpoints of the equations it relates. The legacy record
(`HOLNativeGenericProofCompiler.RawOperations`) withholds most endpoints
(symmetry gets no right side, congruence no second endpoint and no domain),
which suffices for Leibniz equality but not for identity elimination, whose
eliminator takes both endpoints.

`PointedRaw` adds reflexivity at a point, `pointed τ l`. The compiler uses it
at the three reflexivity nodes: `eqRefl`, `beta` and `eta`. A β or η node is
reflexivity between two terms that the selected judgment equates, so it needs
no function extensionality. The point-free reflexivity of the legacy algebra
enters only through the embedding `EqualityRaw.pointedByConstant`.

**Results.**

* The requests of a proof (`requests`) list, with their HOL types, the
  operations its equality nodes need. Compilation succeeds exactly on the
  proofs whose inspected terms are read (`ReadProof`; under a reading that
  interprets every constant, the core proofs, `readProof_iff_isCoreProof`) and
  whose requests are available, for every algebra whose availability does not
  depend on the terms of a node (`compileP_isSome_iff`). Without that
  condition success still implies that no request is refused
  (`compileP_readProof`).
* A proof with no reflexivity node compiles the same way under an algebra and
  under the embedding of its forgetful image (`compileP_forget`).
* Compilation commutes with substitution of the native environment for every
  algebra whose operations do (`compileP_substitute`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.ProofSyntax

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- The rules at the nodes of a proof tree, in prefix order. -/
def rules : {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} → {φ : Formula Const Γ} →
    ProofSyntax Const Δ φ → List RuleTag
  | _, _, _, .hyp _ => [.hyp]
  | _, _, _, .topI => [.topI]
  | _, _, _, .botE p => .botE :: rules p
  | _, _, _, .andI p q => .andI :: (rules p ++ rules q)
  | _, _, _, .andEL p => .andEL :: rules p
  | _, _, _, .andER p => .andER :: rules p
  | _, _, _, .orIL p => .orIL :: rules p
  | _, _, _, .orIR p => .orIR :: rules p
  | _, _, _, .orE p q r => .orE :: (rules p ++ rules q ++ rules r)
  | _, _, _, .impI p => .impI :: rules p
  | _, _, _, .impE p q => .impE :: (rules p ++ rules q)
  | _, _, _, .notI p => .notI :: rules p
  | _, _, _, .notE p q => .notE :: (rules p ++ rules q)
  | _, _, _, .allI p => .allI :: rules p
  | _, _, _, .allE _ p => .allE :: rules p
  | _, _, _, .exI _ p => .exI :: rules p
  | _, _, _, .exE p q => .exE :: (rules p ++ rules q)
  | _, _, _, .eqRefl _ => [.eqRefl]
  | _, _, _, .eqSymm p => .eqSymm :: rules p
  | _, _, _, .eqTrans p q => .eqTrans :: (rules p ++ rules q)
  | _, _, _, .eqPropI p q => .eqPropI :: (rules p ++ rules q)
  | _, _, _, .eqPropEL p => .eqPropEL :: rules p
  | _, _, _, .eqPropER p => .eqPropER :: rules p
  | _, _, _, .eqApp _ p => .eqApp :: rules p
  | _, _, _, .eqAppArg _ p => .eqAppArg :: rules p
  | _, _, _, .eqLam p => .eqLam :: rules p
  | _, _, _, .funExt p => .funExt :: rules p
  | _, _, _, .beta _ _ => [.beta]
  | _, _, _, .eta _ => [.eta]

end Mettapedia.Logic.HOL.ProofSyntax

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative

open Normalization
open Mettapedia.Logic

universe u v

/-! ## Requests -/

/-- An equality operation, at the HOL types of the node that requests it. -/
inductive Request (Base : Type u) : Type u where
  | pointed (τ : HOL.Ty Base)
  | symmetry (τ : HOL.Ty Base)
  | transitivity (τ : HOL.Ty Base)
  | propositionExtensionality
  | propositionForward
  | functionCongruence (σ τ : HOL.Ty Base)
  | argumentCongruence (σ τ : HOL.Ty Base)
  | functionExtensionality (σ τ : HOL.Ty Base)

variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- The operations a proof's equality nodes request, with their types. A
reflexivity node (`eqRefl`, `beta`, `eta`) requests reflexivity at a point;
`eqPropER` requests symmetry at `prop` and then the forward direction;
`eqLam` and `funExt` request function extensionality. -/
def requests : {Γ : HOL.Ctx Base} → {Δ : List (HOL.Formula Const Γ)} →
    {φ : HOL.Formula Const Γ} → HOL.ProofSyntax Const Δ φ → List (Request Base)
  | _, _, _, .hyp _ => []
  | _, _, _, .topI => []
  | _, _, _, .botE p => requests p
  | _, _, _, .andI p q => requests p ++ requests q
  | _, _, _, .andEL p => requests p
  | _, _, _, .andER p => requests p
  | _, _, _, .orIL p => requests p
  | _, _, _, .orIR p => requests p
  | _, _, _, .orE p q r => requests p ++ requests q ++ requests r
  | _, _, _, .impI p => requests p
  | _, _, _, .impE p q => requests p ++ requests q
  | _, _, _, .notI p => requests p
  | _, _, _, .notE p q => requests p ++ requests q
  | _, _, _, .allI p => requests p
  | _, _, _, .allE _ p => requests p
  | _, _, _, .exI _ p => requests p
  | _, _, _, .exE p q => requests p ++ requests q
  | _, _, _, @HOL.ProofSyntax.eqRefl _ _ _ _ τ _ => [.pointed τ]
  | _, _, _, @HOL.ProofSyntax.eqSymm _ _ _ _ τ _ _ p => .symmetry τ :: requests p
  | _, _, _, @HOL.ProofSyntax.eqTrans _ _ _ _ τ _ _ _ p q =>
      .transitivity τ :: (requests p ++ requests q)
  | _, _, _, .eqPropI p q => .propositionExtensionality :: (requests p ++ requests q)
  | _, _, _, .eqPropEL p => .propositionForward :: requests p
  | _, _, _, .eqPropER p => .symmetry .prop :: .propositionForward :: requests p
  | _, _, _, @HOL.ProofSyntax.eqApp _ _ _ _ σ τ _ _ _ p => .functionCongruence σ τ :: requests p
  | _, _, _, @HOL.ProofSyntax.eqAppArg _ _ _ _ σ τ _ _ _ p =>
      .argumentCongruence σ τ :: requests p
  | _, _, _, @HOL.ProofSyntax.eqLam _ _ _ _ σ τ _ _ p => .functionExtensionality σ τ :: requests p
  | _, _, _, @HOL.ProofSyntax.funExt _ _ _ _ σ τ _ _ p =>
      .functionExtensionality σ τ :: requests p
  | _, _, _, @HOL.ProofSyntax.beta _ _ _ _ _ τ _ _ => [.pointed τ]
  | _, _, _, @HOL.ProofSyntax.eta _ _ _ _ σ τ _ => [.pointed (.arr σ τ)]

/-! ## The algebra -/

/-- The computational part of an equality-proof algebra over a reading: the
typed analogue of the legacy `RawOperations`. Each operation receives the HOL
types and the native endpoints of the equations it relates; `reflexivity`
takes no point, as in the legacy algebra. -/
structure EqualityRaw (Head : Type) (Base : Type u) where
  reflexivity : {n : Nat} → Option (Tm Head n)
  /-- From `e : l = r`, a proof of `r = l`: arguments `τ l r e`. -/
  symmetry : {n : Nat} → HOL.Ty Base → Tm Head n → Tm Head n → Tm Head n → Option (Tm Head n)
  /-- From `e₁ : l = m` and `e₂ : m = r`, a proof of `l = r`: arguments `τ l m r e₁ e₂`. -/
  transitivity : {n : Nat} → HOL.Ty Base → Tm Head n → Tm Head n → Tm Head n → Tm Head n →
    Tm Head n → Option (Tm Head n)
  /-- From `f : p → q` and `b : q → p`, a proof of `p = q`: arguments `p q f b`. -/
  propositionExtensionality : {n : Nat} → Tm Head n → Tm Head n → Tm Head n → Tm Head n →
    Option (Tm Head n)
  /-- From `e : p = q`, a proof of `p → q`: arguments `p q e`. -/
  propositionForward : {n : Nat} → Tm Head n → Tm Head n → Tm Head n → Option (Tm Head n)
  /-- From `e : f = g`, a proof of `f a = g a`: arguments `σ τ f g a e`. -/
  functionCongruence : {n : Nat} → HOL.Ty Base → HOL.Ty Base → Tm Head n → Tm Head n →
    Tm Head n → Tm Head n → Option (Tm Head n)
  /-- From `e : l = r`, a proof of `f l = f r`: arguments `σ τ f l r e`. -/
  argumentCongruence : {n : Nat} → HOL.Ty Base → HOL.Ty Base → Tm Head n → Tm Head n →
    Tm Head n → Tm Head n → Option (Tm Head n)
  /-- From `pw : ∀x. f x = g x`, a proof of `f = g`: arguments `σ τ f g pw`. -/
  functionExtensionality : {n : Nat} → HOL.Ty Base → HOL.Ty Base → Tm Head n → Tm Head n →
    Tm Head n → Option (Tm Head n)

/-- An equality-proof algebra with reflexivity at a point: `pointed τ l`
proves `l = r` for every `r` equal to `l`. -/
structure PointedRaw (Head : Type) (Base : Type u) extends EqualityRaw Head Base where
  pointed : {n : Nat} → HOL.Ty Base → Tm Head n → Option (Tm Head n)

/-- The algebra with no equality operation. -/
def EqualityRaw.logicalOnly : EqualityRaw Head Base where
  reflexivity := none
  symmetry := fun _ _ _ _ => none
  transitivity := fun _ _ _ _ _ _ => none
  propositionExtensionality := fun _ _ _ _ => none
  propositionForward := fun _ _ _ => none
  functionCongruence := fun _ _ _ _ _ _ => none
  argumentCongruence := fun _ _ _ _ _ _ => none
  functionExtensionality := fun _ _ _ _ _ => none

/-- The embedding: reflexivity at every point is the point-free reflexivity. -/
def EqualityRaw.pointedByConstant (raw : EqualityRaw Head Base) : PointedRaw Head Base :=
  { raw with pointed := fun _ _ => raw.reflexivity }

/-- The forgetful map. -/
abbrev PointedRaw.forget (raw : PointedRaw Head Base) : EqualityRaw Head Base :=
  raw.toEqualityRaw

@[simp] theorem EqualityRaw.pointedByConstant_forget (raw : EqualityRaw Head Base) :
    raw.pointedByConstant.forget = raw :=
  rfl

/-! ## The compiler -/

namespace HOLReading

section Compile

variable (ρ : HOLReading Head Base Const)

/-- The proof compiler of a reading, over the full retained calculus. The
logical rules compile as in `HOLReading.compile`; the equality rules call the
algebra with the native images of their endpoints, and the rules of the
connectives outside the core are declined. -/
def compileP (ops : PointedRaw Head Base) {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}
    {φ : HOL.Formula Const Γ} (d : HOL.ProofSyntax Const Δ φ) {n : Nat}
    (objects : Sub Head Γ.length n) (hyps : Fin Δ.length → Tm Head n) : Option (Tm Head n) :=
  match d with
  | .hyp i => some (hyps i)
  | @HOL.ProofSyntax.impI _ _ _ _ premise _ body => do
      let _ ← ρ.term premise
      let b ← compileP ops body (fun i => Presentation.rename wk (objects i))
        (Fin.cases (.var 0) (fun i => Presentation.rename wk (hyps i)))
      pure (.lam b)
  | .impE function argument => do
      let f ← compileP ops function objects hyps
      let a ← compileP ops argument objects hyps
      pure (.app f a)
  | .allI body => do
      let b ← compileP ops body (liftSub objects)
        (fun i => Presentation.rename wk (hyps (i.cast (by simp [HOL.weakenHyps]))))
      pure (.lam b)
  | .allE t function => do
      let t' ← ρ.term t
      let f ← compileP ops function objects hyps
      pure (.app f (Presentation.subst objects t'))
  | @HOL.ProofSyntax.eqRefl _ _ _ _ τ t => do
      let t' ← ρ.term t
      ops.pointed τ (Presentation.subst objects t')
  | @HOL.ProofSyntax.eqSymm _ _ _ _ τ left right comparison => do
      let l ← ρ.term left
      let r ← ρ.term right
      let e ← compileP ops comparison objects hyps
      ops.symmetry τ (Presentation.subst objects l) (Presentation.subst objects r) e
  | @HOL.ProofSyntax.eqTrans _ _ _ _ τ left middle right first second => do
      let l ← ρ.term left
      let m ← ρ.term middle
      let r ← ρ.term right
      let e₁ ← compileP ops first objects hyps
      let e₂ ← compileP ops second objects hyps
      ops.transitivity τ (Presentation.subst objects l) (Presentation.subst objects m)
        (Presentation.subst objects r) e₁ e₂
  | @HOL.ProofSyntax.eqPropI _ _ _ _ left right forward backward => do
      let p ← ρ.term left
      let q ← ρ.term right
      let f ← compileP ops forward objects hyps
      let b ← compileP ops backward objects hyps
      ops.propositionExtensionality (Presentation.subst objects p) (Presentation.subst objects q)
        f b
  | @HOL.ProofSyntax.eqPropEL _ _ _ _ left right comparison => do
      let p ← ρ.term left
      let q ← ρ.term right
      let e ← compileP ops comparison objects hyps
      ops.propositionForward (Presentation.subst objects p) (Presentation.subst objects q) e
  | @HOL.ProofSyntax.eqPropER _ _ _ _ left right comparison => do
      let p ← ρ.term left
      let q ← ρ.term right
      let e ← compileP ops comparison objects hyps
      let reversed ← ops.symmetry .prop (Presentation.subst objects p)
        (Presentation.subst objects q) e
      ops.propositionForward (Presentation.subst objects q) (Presentation.subst objects p)
        reversed
  | @HOL.ProofSyntax.eqApp _ _ _ _ σ τ function other argument comparison => do
      let f ← ρ.term function
      let g ← ρ.term other
      let a ← ρ.term argument
      let e ← compileP ops comparison objects hyps
      ops.functionCongruence σ τ (Presentation.subst objects f) (Presentation.subst objects g)
        (Presentation.subst objects a) e
  | @HOL.ProofSyntax.eqAppArg _ _ _ _ σ τ function left right comparison => do
      let f ← ρ.term function
      let l ← ρ.term left
      let r ← ρ.term right
      let e ← compileP ops comparison objects hyps
      ops.argumentCongruence σ τ (Presentation.subst objects f) (Presentation.subst objects l)
        (Presentation.subst objects r) e
  | @HOL.ProofSyntax.eqLam _ _ _ _ σ τ left right comparison => do
      let l ← ρ.term left
      let r ← ρ.term right
      let e ← compileP ops comparison (liftSub objects)
        (fun i => Presentation.rename wk (hyps (i.cast (by simp [HOL.weakenHyps]))))
      ops.functionExtensionality σ τ (.lam (Presentation.subst (liftSub objects) l))
        (.lam (Presentation.subst (liftSub objects) r)) (.lam e)
  | @HOL.ProofSyntax.funExt _ _ _ _ σ τ function other pointwise => do
      let f ← ρ.term function
      let g ← ρ.term other
      let e ← compileP ops pointwise objects hyps
      ops.functionExtensionality σ τ (Presentation.subst objects f) (Presentation.subst objects g) e
  | @HOL.ProofSyntax.beta _ _ _ _ _ τ argument body => do
      let a ← ρ.term argument
      let b ← ρ.term body
      ops.pointed τ (.app (.lam (Presentation.subst (liftSub objects) b))
        (Presentation.subst objects a))
  | @HOL.ProofSyntax.eta _ _ _ _ σ τ function => do
      let f ← ρ.term function
      ops.pointed (.arr σ τ) (.lam (.app (Presentation.rename wk (Presentation.subst objects f))
        (.var 0)))
  | _ => none

/-- The terms a compiled proof inspects are read, and its rules are those of
implication, the universal quantifier and equality: `IsCoreProof` with the
reading in place of the core check. -/
def ReadProof : {Γ : HOL.Ctx Base} → {Δ : List (HOL.Formula Const Γ)} →
    {φ : HOL.Formula Const Γ} → HOL.ProofSyntax Const Δ φ → Prop
  | _, _, _, .hyp _ => True
  | _, _, _, @HOL.ProofSyntax.impI _ _ _ _ premise _ body =>
      (ρ.term premise).isSome ∧ ReadProof body
  | _, _, _, .impE function argument => ReadProof function ∧ ReadProof argument
  | _, _, _, .allI body => ReadProof body
  | _, _, _, .allE t function => (ρ.term t).isSome ∧ ReadProof function
  | _, _, _, .eqRefl t => (ρ.term t).isSome
  | _, _, _, @HOL.ProofSyntax.eqSymm _ _ _ _ _ left right proof =>
      (ρ.term left).isSome ∧ (ρ.term right).isSome ∧ ReadProof proof
  | _, _, _, @HOL.ProofSyntax.eqTrans _ _ _ _ _ left middle right first second =>
      (ρ.term left).isSome ∧ (ρ.term middle).isSome ∧ (ρ.term right).isSome ∧
        ReadProof first ∧ ReadProof second
  | _, _, _, @HOL.ProofSyntax.eqPropI _ _ _ _ left right forward backward =>
      (ρ.term left).isSome ∧ (ρ.term right).isSome ∧ ReadProof forward ∧ ReadProof backward
  | _, _, _, @HOL.ProofSyntax.eqPropEL _ _ _ _ left right proof =>
      (ρ.term left).isSome ∧ (ρ.term right).isSome ∧ ReadProof proof
  | _, _, _, @HOL.ProofSyntax.eqPropER _ _ _ _ left right proof =>
      (ρ.term left).isSome ∧ (ρ.term right).isSome ∧ ReadProof proof
  | _, _, _, @HOL.ProofSyntax.eqApp _ _ _ _ _ _ function other argument proof =>
      (ρ.term function).isSome ∧ (ρ.term other).isSome ∧ (ρ.term argument).isSome ∧
        ReadProof proof
  | _, _, _, @HOL.ProofSyntax.eqAppArg _ _ _ _ _ _ function left right proof =>
      (ρ.term function).isSome ∧ (ρ.term left).isSome ∧ (ρ.term right).isSome ∧
        ReadProof proof
  | _, _, _, @HOL.ProofSyntax.eqLam _ _ _ _ _ _ left right proof =>
      (ρ.term left).isSome ∧ (ρ.term right).isSome ∧ ReadProof proof
  | _, _, _, @HOL.ProofSyntax.funExt _ _ _ _ _ _ function other proof =>
      (ρ.term function).isSome ∧ (ρ.term other).isSome ∧ ReadProof proof
  | _, _, _, .beta t body => (ρ.term t).isSome ∧ (ρ.term body).isSome
  | _, _, _, .eta function => (ρ.term function).isSome
  | _, _, _, _ => False

end Compile

/-! ## Reading and the core fragment -/

section Core

variable {ρ : HOLReading Head Base Const}

open HOL.ImpredicativeConnectives (IsCoreProof IsCore isCore_eq_true_iff)

/-- Under a reading that interprets every constant, a term is read exactly
when it is core. -/
theorem term_isSome_iff_isCore (T : ρ.Total) {Γ : HOL.Ctx Base} {τ : HOL.Ty Base}
    (t : HOL.Term Const Γ τ) : (ρ.term t).isSome ↔ IsCore t := by
  refine ⟨fun read => ?_, fun core => term_isSome_of_isCore T t ((isCore_eq_true_iff t).mpr core)⟩
  obtain ⟨_, h⟩ := Option.isSome_iff_exists.mp read
  exact (isCore_eq_true_iff t).mp (isCore_of_term h)

/-- A read proof is core. -/
theorem ReadProof.isCoreProof {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}
    {φ : HOL.Formula Const Γ} {d : HOL.ProofSyntax Const Δ φ} (read : ρ.ReadProof d) :
    IsCoreProof d := by
  have core : ∀ {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} {t : HOL.Term Const Γ τ},
      (ρ.term t).isSome → IsCore t := fun {_ _ t} h => by
    obtain ⟨_, ht⟩ := Option.isSome_iff_exists.mp h
    exact (isCore_eq_true_iff t).mp (isCore_of_term ht)
  induction d with
  | hyp => trivial
  | _ => simp_all only [ReadProof, IsCoreProof, and_self]

/-- **The domain is the core fragment** under a reading that interprets every
constant. -/
theorem readProof_iff_isCoreProof (T : ρ.Total) {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ} (d : HOL.ProofSyntax Const Δ φ) :
    ρ.ReadProof d ↔ IsCoreProof d := by
  refine ⟨ReadProof.isCoreProof, fun core => ?_⟩
  induction d with
  | hyp => trivial
  | _ => simp_all only [ReadProof, IsCoreProof, term_isSome_iff_isCore T, and_self]

end Core


end HOLReading

/-! ## Availability of the operations -/

namespace PointedRaw

variable (ops : PointedRaw Head Base)

/-- A request is available when its operation succeeds on every term. -/
def Available : Request Base → Prop
  | .pointed τ => ∀ {n : Nat} (l : Tm Head n), (ops.pointed τ l).isSome
  | .symmetry τ => ∀ {n : Nat} (l r e : Tm Head n), (ops.symmetry τ l r e).isSome
  | .transitivity τ => ∀ {n : Nat} (l m r e₁ e₂ : Tm Head n),
      (ops.transitivity τ l m r e₁ e₂).isSome
  | .propositionExtensionality => ∀ {n : Nat} (p q f b : Tm Head n),
      (ops.propositionExtensionality p q f b).isSome
  | .propositionForward => ∀ {n : Nat} (p q e : Tm Head n), (ops.propositionForward p q e).isSome
  | .functionCongruence σ τ => ∀ {n : Nat} (f g a e : Tm Head n),
      (ops.functionCongruence σ τ f g a e).isSome
  | .argumentCongruence σ τ => ∀ {n : Nat} (f l r e : Tm Head n),
      (ops.argumentCongruence σ τ f l r e).isSome
  | .functionExtensionality σ τ => ∀ {n : Nat} (f g pw : Tm Head n),
      (ops.functionExtensionality σ τ f g pw).isSome

/-- A request is refused when its operation fails on every term. -/
def Refuses : Request Base → Prop
  | .pointed τ => ∀ {n : Nat} (l : Tm Head n), ops.pointed τ l = none
  | .symmetry τ => ∀ {n : Nat} (l r e : Tm Head n), ops.symmetry τ l r e = none
  | .transitivity τ => ∀ {n : Nat} (l m r e₁ e₂ : Tm Head n),
      ops.transitivity τ l m r e₁ e₂ = none
  | .propositionExtensionality => ∀ {n : Nat} (p q f b : Tm Head n),
      ops.propositionExtensionality p q f b = none
  | .propositionForward => ∀ {n : Nat} (p q e : Tm Head n), ops.propositionForward p q e = none
  | .functionCongruence σ τ => ∀ {n : Nat} (f g a e : Tm Head n),
      ops.functionCongruence σ τ f g a e = none
  | .argumentCongruence σ τ => ∀ {n : Nat} (f l r e : Tm Head n),
      ops.argumentCongruence σ τ f l r e = none
  | .functionExtensionality σ τ => ∀ {n : Nat} (f g pw : Tm Head n),
      ops.functionExtensionality σ τ f g pw = none

/-- The availability of every operation depends only on the HOL types of the
node, not on its terms: each request is available or refused. -/
def TermUniform : Prop := ∀ q : Request Base, ops.Available q ∨ ops.Refuses q

variable {ops}

/-- A request is not both available and refused. -/
theorem not_refuses_of_available {q : Request Base} (available : ops.Available q) :
    ¬ ops.Refuses q := by
  intro refuses
  have z : Tm Head 0 := .const .anonymous
  cases q with
  | pointed τ =>
      have h := available z
      rw [refuses] at h
      exact Bool.false_ne_true h
  | symmetry τ =>
      have h := available z z z
      rw [refuses] at h
      exact Bool.false_ne_true h
  | transitivity τ =>
      have h := available z z z z z
      rw [refuses] at h
      exact Bool.false_ne_true h
  | propositionExtensionality =>
      have h := available z z z z
      rw [refuses] at h
      exact Bool.false_ne_true h
  | propositionForward =>
      have h := available z z z
      rw [refuses] at h
      exact Bool.false_ne_true h
  | functionCongruence σ τ =>
      have h := available z z z z
      rw [refuses] at h
      exact Bool.false_ne_true h
  | argumentCongruence σ τ =>
      have h := available z z z z
      rw [refuses] at h
      exact Bool.false_ne_true h
  | functionExtensionality σ τ =>
      have h := available z z z
      rw [refuses] at h
      exact Bool.false_ne_true h

/-- Under term uniformity, a request that is not refused is available. -/
theorem TermUniform.available (uniform : ops.TermUniform) {q : Request Base}
    (notRefused : ¬ ops.Refuses q) : ops.Available q :=
  (uniform q).resolve_right notRefused

/-! ### An operation that succeeds somewhere is not refused -/

theorem not_refuses_pointed {τ : HOL.Ty Base} {n : Nat} {l : Tm Head n}
    (h : (ops.pointed τ l).isSome) : ¬ ops.Refuses (.pointed τ) := fun refuses => by
  have none := refuses l
  rw [none] at h
  exact Bool.false_ne_true h

theorem not_refuses_symmetry {τ : HOL.Ty Base} {n : Nat} {l r e : Tm Head n}
    (h : (ops.symmetry τ l r e).isSome) : ¬ ops.Refuses (.symmetry τ) := fun refuses => by
  have none := refuses l r e
  rw [none] at h
  exact Bool.false_ne_true h

theorem not_refuses_transitivity {τ : HOL.Ty Base} {n : Nat} {l m r e₁ e₂ : Tm Head n}
    (h : (ops.transitivity τ l m r e₁ e₂).isSome) : ¬ ops.Refuses (.transitivity τ) :=
  fun refuses => by
    have none := refuses l m r e₁ e₂
    rw [none] at h
    exact Bool.false_ne_true h

theorem not_refuses_propositionExtensionality {n : Nat} {p q f b : Tm Head n}
    (h : (ops.propositionExtensionality p q f b).isSome) :
    ¬ ops.Refuses .propositionExtensionality := fun refuses => by
  have none := refuses p q f b
  rw [none] at h
  exact Bool.false_ne_true h

theorem not_refuses_propositionForward {n : Nat} {p q e : Tm Head n}
    (h : (ops.propositionForward p q e).isSome) : ¬ ops.Refuses .propositionForward :=
  fun refuses => by
    have none := refuses p q e
    rw [none] at h
    exact Bool.false_ne_true h

theorem not_refuses_functionCongruence {σ τ : HOL.Ty Base} {n : Nat} {f g a e : Tm Head n}
    (h : (ops.functionCongruence σ τ f g a e).isSome) :
    ¬ ops.Refuses (.functionCongruence σ τ) := fun refuses => by
  have none := refuses f g a e
  rw [none] at h
  exact Bool.false_ne_true h

theorem not_refuses_argumentCongruence {σ τ : HOL.Ty Base} {n : Nat} {f l r e : Tm Head n}
    (h : (ops.argumentCongruence σ τ f l r e).isSome) :
    ¬ ops.Refuses (.argumentCongruence σ τ) := fun refuses => by
  have none := refuses f l r e
  rw [none] at h
  exact Bool.false_ne_true h

theorem not_refuses_functionExtensionality {σ τ : HOL.Ty Base} {n : Nat} {f g pw : Tm Head n}
    (h : (ops.functionExtensionality σ τ f g pw).isSome) :
    ¬ ops.Refuses (.functionExtensionality σ τ) := fun refuses => by
  have none := refuses f g pw
  rw [none] at h
  exact Bool.false_ne_true h

end PointedRaw

namespace HOLReading

variable {ρ : HOLReading Head Base Const}

private theorem bind_isSome {α β : Type} {input : Option α} {next : α → Option β}
    (available : input.isSome) (continued : ∀ value, (next value).isSome) :
    (input.bind next).isSome := by
  cases input with
  | none => contradiction
  | some value => exact continued value

private theorem isSome_of_bind {α β : Type} {input : Option α} {next : α → Option β}
    (h : (input.bind next).isSome) : input.isSome := by
  cases input with
  | none => contradiction
  | some _ => rfl

private theorem next_of_bind {α β : Type} {input : Option α} {next : α → Option β}
    {value : α} (h : (input.bind next).isSome) (hv : input = some value) :
    (next value).isSome := by
  subst hv
  exact h

/-- **Completeness of the compiler on its domain.** A read proof whose requests
are available compiles, in every environment. -/
theorem compileP_isSome_of {ops : PointedRaw Head Base} {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ} {d : HOL.ProofSyntax Const Δ φ}
    (read : ρ.ReadProof d) (covered : ∀ q ∈ requests d, ops.Available q) {n : Nat}
    (objects : Sub Head Γ.length n) (hyps : Fin Δ.length → Tm Head n) :
    (ρ.compileP ops d objects hyps).isSome := by
  induction d generalizing n with
  | hyp => rfl
  | impI body ih =>
      obtain ⟨premise, readBody⟩ := read
      exact bind_isSome premise fun _ => bind_isSome (ih readBody covered _ _) fun _ => rfl
  | impE function argument ihf iha =>
      obtain ⟨readF, readA⟩ := read
      exact bind_isSome (ihf readF (fun q m => covered q (List.mem_append_left _ m)) _ _)
        fun _ => bind_isSome (iha readA (fun q m => covered q (List.mem_append_right _ m)) _ _)
          fun _ => rfl
  | allI body ih => exact bind_isSome (ih read covered _ _) fun _ => rfl
  | allE t function ih =>
      obtain ⟨readT, readF⟩ := read
      exact bind_isSome readT fun _ => bind_isSome (ih readF covered _ _) fun _ => rfl
  | eqRefl t =>
      have avail : ops.Available (.pointed _) := covered _ (List.mem_singleton_self _)
      exact bind_isSome read fun _ => avail _
  | eqSymm proof ih =>
      obtain ⟨readL, readR, readP⟩ := read
      have avail : ops.Available (.symmetry _) := covered _ List.mem_cons_self
      exact bind_isSome readL fun _ => bind_isSome readR fun _ =>
        bind_isSome (ih readP (fun q m => covered q (List.mem_cons_of_mem _ m)) _ _)
          fun _ => avail _ _ _
  | eqTrans first second ihFirst ihSecond =>
      obtain ⟨readL, readM, readR, readFirst, readSecond⟩ := read
      have avail : ops.Available (.transitivity _) := covered _ List.mem_cons_self
      exact bind_isSome readL fun _ => bind_isSome readM fun _ => bind_isSome readR fun _ =>
        bind_isSome (ihFirst readFirst (fun q m => covered q
          (List.mem_cons_of_mem _ (List.mem_append_left _ m))) _ _) fun _ =>
        bind_isSome (ihSecond readSecond (fun q m => covered q
          (List.mem_cons_of_mem _ (List.mem_append_right _ m))) _ _) fun _ => avail _ _ _ _ _
  | eqPropI forward backward ihForward ihBackward =>
      obtain ⟨readL, readR, readForward, readBackward⟩ := read
      have avail : ops.Available .propositionExtensionality := covered _ List.mem_cons_self
      exact bind_isSome readL fun _ => bind_isSome readR fun _ =>
        bind_isSome (ihForward readForward (fun q m => covered q
          (List.mem_cons_of_mem _ (List.mem_append_left _ m))) _ _) fun _ =>
        bind_isSome (ihBackward readBackward (fun q m => covered q
          (List.mem_cons_of_mem _ (List.mem_append_right _ m))) _ _) fun _ => avail _ _ _ _
  | eqPropEL proof ih =>
      obtain ⟨readL, readR, readP⟩ := read
      have avail : ops.Available .propositionForward := covered _ List.mem_cons_self
      exact bind_isSome readL fun _ => bind_isSome readR fun _ =>
        bind_isSome (ih readP (fun q m => covered q (List.mem_cons_of_mem _ m)) _ _)
          fun _ => avail _ _ _
  | eqPropER proof ih =>
      obtain ⟨readL, readR, readP⟩ := read
      have symmetric : ops.Available (.symmetry .prop) := covered _ List.mem_cons_self
      have forward : ops.Available .propositionForward :=
        covered _ (List.mem_cons_of_mem _ List.mem_cons_self)
      exact bind_isSome readL fun _ => bind_isSome readR fun _ =>
        bind_isSome (ih readP (fun q m => covered q
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ m))) _ _) fun _ =>
        bind_isSome (symmetric _ _ _) fun _ => forward _ _ _
  | eqApp argument proof ih =>
      obtain ⟨readF, readG, readA, readP⟩ := read
      have avail : ops.Available (.functionCongruence _ _) := covered _ List.mem_cons_self
      exact bind_isSome readF fun _ => bind_isSome readG fun _ => bind_isSome readA fun _ =>
        bind_isSome (ih readP (fun q m => covered q (List.mem_cons_of_mem _ m)) _ _)
          fun _ => avail _ _ _ _
  | eqAppArg function proof ih =>
      obtain ⟨readF, readL, readR, readP⟩ := read
      have avail : ops.Available (.argumentCongruence _ _) := covered _ List.mem_cons_self
      exact bind_isSome readF fun _ => bind_isSome readL fun _ => bind_isSome readR fun _ =>
        bind_isSome (ih readP (fun q m => covered q (List.mem_cons_of_mem _ m)) _ _)
          fun _ => avail _ _ _ _
  | eqLam proof ih =>
      obtain ⟨readL, readR, readP⟩ := read
      have avail : ops.Available (.functionExtensionality _ _) := covered _ List.mem_cons_self
      exact bind_isSome readL fun _ => bind_isSome readR fun _ =>
        bind_isSome (ih readP (fun q m => covered q (List.mem_cons_of_mem _ m)) _ _)
          fun _ => avail _ _ _
  | funExt proof ih =>
      obtain ⟨readF, readG, readP⟩ := read
      have avail : ops.Available (.functionExtensionality _ _) := covered _ List.mem_cons_self
      exact bind_isSome readF fun _ => bind_isSome readG fun _ =>
        bind_isSome (ih readP (fun q m => covered q (List.mem_cons_of_mem _ m)) _ _)
          fun _ => avail _ _ _
  | beta t body =>
      obtain ⟨readT, readBody⟩ := read
      have avail : ops.Available (.pointed _) := covered _ (List.mem_singleton_self _)
      exact bind_isSome readT fun _ => bind_isSome readBody fun _ => avail _
  | eta function =>
      have avail : ops.Available (.pointed _) := covered _ (List.mem_singleton_self _)
      exact bind_isSome read fun _ => avail _
  | _ => exact read.elim

/-- **Soundness of the domain.** A proof that compiles is read, and none of its
requests is refused. -/
theorem compileP_readProof {ops : PointedRaw Head Base} {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ} {d : HOL.ProofSyntax Const Δ φ}
    {n : Nat} {objects : Sub Head Γ.length n} {hyps : Fin Δ.length → Tm Head n}
    (success : (ρ.compileP ops d objects hyps).isSome) :
    ρ.ReadProof d ∧ ∀ q ∈ requests d, ¬ ops.Refuses q := by
  induction d generalizing n with
  | hyp => exact ⟨trivial, fun _ m => absurd m List.not_mem_nil⟩
  | impI body ih =>
      have s₁ := isSome_of_bind success
      obtain ⟨_, h₁⟩ := Option.isSome_iff_exists.mp s₁
      have r₁ := next_of_bind success h₁
      obtain ⟨readB, reqB⟩ := ih (isSome_of_bind r₁)
      exact ⟨⟨s₁, readB⟩, reqB⟩
  | impE function argument ihf iha =>
      have s₁ := isSome_of_bind success
      obtain ⟨_, h₁⟩ := Option.isSome_iff_exists.mp s₁
      have r₁ := next_of_bind success h₁
      obtain ⟨readF, reqF⟩ := ihf s₁
      obtain ⟨readA, reqA⟩ := iha (isSome_of_bind r₁)
      refine ⟨⟨readF, readA⟩, fun q m => ?_⟩
      rcases List.mem_append.mp m with m | m
      · exact reqF q m
      · exact reqA q m
  | allI body ih =>
      obtain ⟨readB, reqB⟩ := ih (isSome_of_bind success)
      exact ⟨readB, reqB⟩
  | allE t function ih =>
      have s₁ := isSome_of_bind success
      obtain ⟨_, h₁⟩ := Option.isSome_iff_exists.mp s₁
      have r₁ := next_of_bind success h₁
      obtain ⟨readF, reqF⟩ := ih (isSome_of_bind r₁)
      exact ⟨⟨s₁, readF⟩, reqF⟩
  | eqRefl t =>
      have s₁ := isSome_of_bind success
      obtain ⟨_, h₁⟩ := Option.isSome_iff_exists.mp s₁
      have r₁ := next_of_bind success h₁
      refine ⟨s₁, fun q m => ?_⟩
      rw [List.mem_singleton.mp m]
      exact PointedRaw.not_refuses_pointed r₁
  | eqSymm proof ih =>
      have s₁ := isSome_of_bind success
      obtain ⟨_, h₁⟩ := Option.isSome_iff_exists.mp s₁
      have r₁ := next_of_bind success h₁
      have s₂ := isSome_of_bind r₁
      obtain ⟨_, h₂⟩ := Option.isSome_iff_exists.mp s₂
      have r₂ := next_of_bind r₁ h₂
      have s₃ := isSome_of_bind r₂
      obtain ⟨_, h₃⟩ := Option.isSome_iff_exists.mp s₃
      have r₃ := next_of_bind r₂ h₃
      obtain ⟨readP, reqP⟩ := ih s₃
      refine ⟨⟨s₁, s₂, readP⟩, fun q m => ?_⟩
      rcases List.mem_cons.mp m with rfl | m
      · exact PointedRaw.not_refuses_symmetry r₃
      · exact reqP q m
  | eqTrans first second ihFirst ihSecond =>
      have s₁ := isSome_of_bind success
      obtain ⟨_, h₁⟩ := Option.isSome_iff_exists.mp s₁
      have r₁ := next_of_bind success h₁
      have s₂ := isSome_of_bind r₁
      obtain ⟨_, h₂⟩ := Option.isSome_iff_exists.mp s₂
      have r₂ := next_of_bind r₁ h₂
      have s₃ := isSome_of_bind r₂
      obtain ⟨_, h₃⟩ := Option.isSome_iff_exists.mp s₃
      have r₃ := next_of_bind r₂ h₃
      have s₄ := isSome_of_bind r₃
      obtain ⟨_, h₄⟩ := Option.isSome_iff_exists.mp s₄
      have r₄ := next_of_bind r₃ h₄
      have s₅ := isSome_of_bind r₄
      obtain ⟨_, h₅⟩ := Option.isSome_iff_exists.mp s₅
      have r₅ := next_of_bind r₄ h₅
      obtain ⟨readFirst, reqFirst⟩ := ihFirst s₄
      obtain ⟨readSecond, reqSecond⟩ := ihSecond s₅
      refine ⟨⟨s₁, s₂, s₃, readFirst, readSecond⟩, fun q m => ?_⟩
      rcases List.mem_cons.mp m with rfl | m
      · exact PointedRaw.not_refuses_transitivity r₅
      · rcases List.mem_append.mp m with m | m
        · exact reqFirst q m
        · exact reqSecond q m
  | eqPropI forward backward ihForward ihBackward =>
      have s₁ := isSome_of_bind success
      obtain ⟨_, h₁⟩ := Option.isSome_iff_exists.mp s₁
      have r₁ := next_of_bind success h₁
      have s₂ := isSome_of_bind r₁
      obtain ⟨_, h₂⟩ := Option.isSome_iff_exists.mp s₂
      have r₂ := next_of_bind r₁ h₂
      have s₃ := isSome_of_bind r₂
      obtain ⟨_, h₃⟩ := Option.isSome_iff_exists.mp s₃
      have r₃ := next_of_bind r₂ h₃
      have s₄ := isSome_of_bind r₃
      obtain ⟨_, h₄⟩ := Option.isSome_iff_exists.mp s₄
      have r₄ := next_of_bind r₃ h₄
      obtain ⟨readForward, reqForward⟩ := ihForward s₃
      obtain ⟨readBackward, reqBackward⟩ := ihBackward s₄
      refine ⟨⟨s₁, s₂, readForward, readBackward⟩, fun q m => ?_⟩
      rcases List.mem_cons.mp m with rfl | m
      · exact PointedRaw.not_refuses_propositionExtensionality r₄
      · rcases List.mem_append.mp m with m | m
        · exact reqForward q m
        · exact reqBackward q m
  | eqPropEL proof ih =>
      have s₁ := isSome_of_bind success
      obtain ⟨_, h₁⟩ := Option.isSome_iff_exists.mp s₁
      have r₁ := next_of_bind success h₁
      have s₂ := isSome_of_bind r₁
      obtain ⟨_, h₂⟩ := Option.isSome_iff_exists.mp s₂
      have r₂ := next_of_bind r₁ h₂
      have s₃ := isSome_of_bind r₂
      obtain ⟨_, h₃⟩ := Option.isSome_iff_exists.mp s₃
      have r₃ := next_of_bind r₂ h₃
      obtain ⟨readP, reqP⟩ := ih s₃
      refine ⟨⟨s₁, s₂, readP⟩, fun q m => ?_⟩
      rcases List.mem_cons.mp m with rfl | m
      · exact PointedRaw.not_refuses_propositionForward r₃
      · exact reqP q m
  | eqPropER proof ih =>
      have s₁ := isSome_of_bind success
      obtain ⟨_, h₁⟩ := Option.isSome_iff_exists.mp s₁
      have r₁ := next_of_bind success h₁
      have s₂ := isSome_of_bind r₁
      obtain ⟨_, h₂⟩ := Option.isSome_iff_exists.mp s₂
      have r₂ := next_of_bind r₁ h₂
      have s₃ := isSome_of_bind r₂
      obtain ⟨_, h₃⟩ := Option.isSome_iff_exists.mp s₃
      have r₃ := next_of_bind r₂ h₃
      have s₄ := isSome_of_bind r₃
      obtain ⟨_, h₄⟩ := Option.isSome_iff_exists.mp s₄
      have r₄ := next_of_bind r₃ h₄
      obtain ⟨readP, reqP⟩ := ih s₃
      refine ⟨⟨s₁, s₂, readP⟩, fun q m => ?_⟩
      rcases List.mem_cons.mp m with rfl | m
      · exact PointedRaw.not_refuses_symmetry s₄
      · rcases List.mem_cons.mp m with rfl | m
        · exact PointedRaw.not_refuses_propositionForward r₄
        · exact reqP q m
  | eqApp argument proof ih =>
      have s₁ := isSome_of_bind success
      obtain ⟨_, h₁⟩ := Option.isSome_iff_exists.mp s₁
      have r₁ := next_of_bind success h₁
      have s₂ := isSome_of_bind r₁
      obtain ⟨_, h₂⟩ := Option.isSome_iff_exists.mp s₂
      have r₂ := next_of_bind r₁ h₂
      have s₃ := isSome_of_bind r₂
      obtain ⟨_, h₃⟩ := Option.isSome_iff_exists.mp s₃
      have r₃ := next_of_bind r₂ h₃
      have s₄ := isSome_of_bind r₃
      obtain ⟨_, h₄⟩ := Option.isSome_iff_exists.mp s₄
      have r₄ := next_of_bind r₃ h₄
      obtain ⟨readP, reqP⟩ := ih s₄
      refine ⟨⟨s₁, s₂, s₃, readP⟩, fun q m => ?_⟩
      rcases List.mem_cons.mp m with rfl | m
      · exact PointedRaw.not_refuses_functionCongruence r₄
      · exact reqP q m
  | eqAppArg function proof ih =>
      have s₁ := isSome_of_bind success
      obtain ⟨_, h₁⟩ := Option.isSome_iff_exists.mp s₁
      have r₁ := next_of_bind success h₁
      have s₂ := isSome_of_bind r₁
      obtain ⟨_, h₂⟩ := Option.isSome_iff_exists.mp s₂
      have r₂ := next_of_bind r₁ h₂
      have s₃ := isSome_of_bind r₂
      obtain ⟨_, h₃⟩ := Option.isSome_iff_exists.mp s₃
      have r₃ := next_of_bind r₂ h₃
      have s₄ := isSome_of_bind r₃
      obtain ⟨_, h₄⟩ := Option.isSome_iff_exists.mp s₄
      have r₄ := next_of_bind r₃ h₄
      obtain ⟨readP, reqP⟩ := ih s₄
      refine ⟨⟨s₁, s₂, s₃, readP⟩, fun q m => ?_⟩
      rcases List.mem_cons.mp m with rfl | m
      · exact PointedRaw.not_refuses_argumentCongruence r₄
      · exact reqP q m
  | eqLam proof ih =>
      have s₁ := isSome_of_bind success
      obtain ⟨_, h₁⟩ := Option.isSome_iff_exists.mp s₁
      have r₁ := next_of_bind success h₁
      have s₂ := isSome_of_bind r₁
      obtain ⟨_, h₂⟩ := Option.isSome_iff_exists.mp s₂
      have r₂ := next_of_bind r₁ h₂
      have s₃ := isSome_of_bind r₂
      obtain ⟨_, h₃⟩ := Option.isSome_iff_exists.mp s₃
      have r₃ := next_of_bind r₂ h₃
      obtain ⟨readP, reqP⟩ := ih s₃
      refine ⟨⟨s₁, s₂, readP⟩, fun q m => ?_⟩
      rcases List.mem_cons.mp m with rfl | m
      · exact PointedRaw.not_refuses_functionExtensionality r₃
      · exact reqP q m
  | funExt proof ih =>
      have s₁ := isSome_of_bind success
      obtain ⟨_, h₁⟩ := Option.isSome_iff_exists.mp s₁
      have r₁ := next_of_bind success h₁
      have s₂ := isSome_of_bind r₁
      obtain ⟨_, h₂⟩ := Option.isSome_iff_exists.mp s₂
      have r₂ := next_of_bind r₁ h₂
      have s₃ := isSome_of_bind r₂
      obtain ⟨_, h₃⟩ := Option.isSome_iff_exists.mp s₃
      have r₃ := next_of_bind r₂ h₃
      obtain ⟨readP, reqP⟩ := ih s₃
      refine ⟨⟨s₁, s₂, readP⟩, fun q m => ?_⟩
      rcases List.mem_cons.mp m with rfl | m
      · exact PointedRaw.not_refuses_functionExtensionality r₃
      · exact reqP q m
  | beta t body =>
      have s₁ := isSome_of_bind success
      obtain ⟨_, h₁⟩ := Option.isSome_iff_exists.mp s₁
      have r₁ := next_of_bind success h₁
      have s₂ := isSome_of_bind r₁
      obtain ⟨_, h₂⟩ := Option.isSome_iff_exists.mp s₂
      have r₂ := next_of_bind r₁ h₂
      refine ⟨⟨s₁, s₂⟩, fun q m => ?_⟩
      rw [List.mem_singleton.mp m]
      exact PointedRaw.not_refuses_pointed r₂
  | eta function =>
      have s₁ := isSome_of_bind success
      obtain ⟨_, h₁⟩ := Option.isSome_iff_exists.mp s₁
      have r₁ := next_of_bind success h₁
      refine ⟨s₁, fun q m => ?_⟩
      rw [List.mem_singleton.mp m]
      exact PointedRaw.not_refuses_pointed r₁
  | _ => exact absurd success (by simp [compileP])

/-- **Exact totality.** For an algebra whose availability depends only on the
types of a node, a proof compiles exactly when it is read and every operation
it requests is available. -/
theorem compileP_isSome_iff {ops : PointedRaw Head Base} (uniform : ops.TermUniform)
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntax Const Δ φ) {n : Nat} (objects : Sub Head Γ.length n)
    (hyps : Fin Δ.length → Tm Head n) :
    (ρ.compileP ops d objects hyps).isSome ↔
      ρ.ReadProof d ∧ ∀ q ∈ requests d, ops.Available q := by
  refine ⟨fun success => ?_, fun ⟨read, covered⟩ => compileP_isSome_of read covered objects hyps⟩
  obtain ⟨read, notRefused⟩ := compileP_readProof success
  exact ⟨read, fun q m => uniform.available (notRefused q m)⟩

/-- **Exact totality on the core fragment**, under a reading that interprets
every constant. -/
theorem compileP_isSome_iff_isCoreProof (T : ρ.Total) {ops : PointedRaw Head Base}
    (uniform : ops.TermUniform) {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}
    {φ : HOL.Formula Const Γ} (d : HOL.ProofSyntax Const Δ φ) {n : Nat}
    (objects : Sub Head Γ.length n) (hyps : Fin Δ.length → Tm Head n) :
    (ρ.compileP ops d objects hyps).isSome ↔
      HOL.ImpredicativeConnectives.IsCoreProof d ∧ ∀ q ∈ requests d, ops.Available q := by
  rw [compileP_isSome_iff uniform, readProof_iff_isCoreProof T]

/-! ## The forgetful map -/

/-- The compiler reads `pointed` only at reflexivity nodes: two algebras with
the same forgetful image compile every proof with no reflexivity node to the
same result. -/
theorem compileP_congr {ops ops' : PointedRaw Head Base} (same : ops.forget = ops'.forget)
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntax Const Δ φ) (noPointed : ∀ τ, Request.pointed τ ∉ requests d) {n : Nat}
    (objects : Sub Head Γ.length n) (hyps : Fin Δ.length → Tm Head n) :
    ρ.compileP ops d objects hyps = ρ.compileP ops' d objects hyps := by
  obtain ⟨raw, pointed⟩ := ops
  obtain ⟨raw', pointed'⟩ := ops'
  simp only [PointedRaw.forget] at same
  subst same
  induction d generalizing n with
  | hyp => rfl
  | impI body ih => simp only [compileP, ih noPointed]
  | impE function argument ihf iha =>
      simp only [compileP,
        ihf (fun τ m => noPointed τ (List.mem_append_left _ m)),
        iha (fun τ m => noPointed τ (List.mem_append_right _ m))]
  | allI body ih => simp only [compileP, ih noPointed]
  | allE t function ih => simp only [compileP, ih noPointed]
  | eqRefl t => exact absurd (List.mem_singleton_self _) (noPointed _)
  | eqSymm proof ih =>
      simp only [compileP, ih (fun τ m => noPointed τ (List.mem_cons_of_mem _ m))]
  | eqTrans first second ihFirst ihSecond =>
      simp only [compileP,
        ihFirst (fun τ m => noPointed τ (List.mem_cons_of_mem _ (List.mem_append_left _ m))),
        ihSecond (fun τ m => noPointed τ (List.mem_cons_of_mem _ (List.mem_append_right _ m)))]
  | eqPropI forward backward ihForward ihBackward =>
      simp only [compileP,
        ihForward (fun τ m => noPointed τ (List.mem_cons_of_mem _ (List.mem_append_left _ m))),
        ihBackward (fun τ m => noPointed τ (List.mem_cons_of_mem _ (List.mem_append_right _ m)))]
  | eqPropEL proof ih =>
      simp only [compileP, ih (fun τ m => noPointed τ (List.mem_cons_of_mem _ m))]
  | eqPropER proof ih =>
      simp only [compileP,
        ih (fun τ m => noPointed τ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ m)))]
  | eqApp argument proof ih =>
      simp only [compileP, ih (fun τ m => noPointed τ (List.mem_cons_of_mem _ m))]
  | eqAppArg function proof ih =>
      simp only [compileP, ih (fun τ m => noPointed τ (List.mem_cons_of_mem _ m))]
  | eqLam proof ih =>
      simp only [compileP, ih (fun τ m => noPointed τ (List.mem_cons_of_mem _ m))]
  | funExt proof ih =>
      simp only [compileP, ih (fun τ m => noPointed τ (List.mem_cons_of_mem _ m))]
  | beta t body => exact absurd (List.mem_singleton_self _) (noPointed _)
  | eta function => exact absurd (List.mem_singleton_self _) (noPointed _)
  | _ => rfl

/-- **Forgetful map.** A proof with no reflexivity node compiles the same way
under an algebra and under the embedding of its forgetful image. -/
theorem compileP_forget (ops : PointedRaw Head Base) {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ} (d : HOL.ProofSyntax Const Δ φ)
    (noPointed : ∀ τ, Request.pointed τ ∉ requests d) {n : Nat}
    (objects : Sub Head Γ.length n) (hyps : Fin Δ.length → Tm Head n) :
    ρ.compileP ops d objects hyps = ρ.compileP ops.forget.pointedByConstant d objects hyps :=
  compileP_congr (ops := ops) (ops' := ops.forget.pointedByConstant) rfl d noPointed objects hyps

end HOLReading

/-! ## Substitution -/

/-- Each operation commutes with substitution of the native environment,
including its availability. -/
structure PointedRaw.Natural (ops : PointedRaw Head Base) : Prop where
  reflexivity : ∀ {n m : Nat} (σ : Sub Head n m),
    (ops.reflexivity : Option (Tm Head m)) = ops.reflexivity.map (Presentation.subst σ)
  pointed : ∀ {n m : Nat} (σ : Sub Head n m) (τ : HOL.Ty Base) (l : Tm Head n),
    ops.pointed τ (Presentation.subst σ l) = (ops.pointed τ l).map (Presentation.subst σ)
  symmetry : ∀ {n m : Nat} (σ : Sub Head n m) (τ : HOL.Ty Base) (l r e : Tm Head n),
    ops.symmetry τ (Presentation.subst σ l) (Presentation.subst σ r) (Presentation.subst σ e) =
      (ops.symmetry τ l r e).map (Presentation.subst σ)
  transitivity : ∀ {n m : Nat} (σ : Sub Head n m) (τ : HOL.Ty Base) (l mid r e₁ e₂ : Tm Head n),
    ops.transitivity τ (Presentation.subst σ l) (Presentation.subst σ mid)
        (Presentation.subst σ r) (Presentation.subst σ e₁) (Presentation.subst σ e₂) =
      (ops.transitivity τ l mid r e₁ e₂).map (Presentation.subst σ)
  propositionExtensionality : ∀ {n m : Nat} (σ : Sub Head n m) (p q f b : Tm Head n),
    ops.propositionExtensionality (Presentation.subst σ p) (Presentation.subst σ q)
        (Presentation.subst σ f) (Presentation.subst σ b) =
      (ops.propositionExtensionality p q f b).map (Presentation.subst σ)
  propositionForward : ∀ {n m : Nat} (σ : Sub Head n m) (p q e : Tm Head n),
    ops.propositionForward (Presentation.subst σ p) (Presentation.subst σ q)
        (Presentation.subst σ e) =
      (ops.propositionForward p q e).map (Presentation.subst σ)
  functionCongruence : ∀ {n m : Nat} (σ : Sub Head n m) (s τ : HOL.Ty Base) (f g a e : Tm Head n),
    ops.functionCongruence s τ (Presentation.subst σ f) (Presentation.subst σ g)
        (Presentation.subst σ a) (Presentation.subst σ e) =
      (ops.functionCongruence s τ f g a e).map (Presentation.subst σ)
  argumentCongruence : ∀ {n m : Nat} (σ : Sub Head n m) (s τ : HOL.Ty Base) (f l r e : Tm Head n),
    ops.argumentCongruence s τ (Presentation.subst σ f) (Presentation.subst σ l)
        (Presentation.subst σ r) (Presentation.subst σ e) =
      (ops.argumentCongruence s τ f l r e).map (Presentation.subst σ)
  functionExtensionality : ∀ {n m : Nat} (σ : Sub Head n m) (s τ : HOL.Ty Base)
      (f g pw : Tm Head n),
    ops.functionExtensionality s τ (Presentation.subst σ f) (Presentation.subst σ g)
        (Presentation.subst σ pw) =
      (ops.functionExtensionality s τ f g pw).map (Presentation.subst σ)

theorem EqualityRaw.logicalOnly_pointedByConstant_natural :
    (EqualityRaw.logicalOnly : EqualityRaw Head Base).pointedByConstant.Natural := by
  constructor <;> intros <;> rfl

namespace HOLReading

variable {ρ : HOLReading Head Base Const}

private theorem subst_comp_apply {n m k : Nat} (σ : Sub Head m k) (objects : Sub Head n m)
    (t : Tm Head n) :
    Presentation.subst (fun i => Presentation.subst σ (objects i)) t =
      Presentation.subst σ (Presentation.subst objects t) :=
  (subst_comp σ objects t).symm

private theorem liftSub_comp {n m k : Nat} (σ : Sub Head m k) (objects : Sub Head n m) :
    liftSub (fun i => Presentation.subst σ (objects i)) =
      fun i => Presentation.subst (liftSub σ) (liftSub objects i) := by
  funext i
  exact (liftSub_comp_apply σ objects i).symm

/-- **Substitution naturality of the compiler.** Compiling after moving the
native environment along a substitution, or moving the result, agree,
including on the proofs the compiler declines. -/
theorem compileP_substitute {ops : PointedRaw Head Base} (natural : ops.Natural)
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntax Const Δ φ) {n m : Nat} (objects : Sub Head Γ.length n)
    (hyps : Fin Δ.length → Tm Head n) (σ : Sub Head n m) :
    ρ.compileP ops d (fun i => Presentation.subst σ (objects i))
        (fun i => Presentation.subst σ (hyps i)) =
      (ρ.compileP ops d objects hyps).map (Presentation.subst σ) := by
  induction d generalizing n m with
  | hyp i => rfl
  | @impI Γ Δ p q body ih =>
      have obj : (fun i => Presentation.rename wk (Presentation.subst σ (objects i))) =
          (fun i => Presentation.subst (liftSub σ) (Presentation.rename wk (objects i))) := by
        funext i
        simp only [subst_liftSub_wk]
      have hyp : (Fin.cases (.var 0) (fun i => Presentation.rename wk
            (Presentation.subst σ (hyps i))) : Fin (p :: Δ).length → Tm Head (m + 1)) =
          (fun i => Presentation.subst (liftSub σ)
            (Fin.cases (.var 0) (fun j => Presentation.rename wk (hyps j)) i)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · simp only [Fin.cases_succ, subst_liftSub_wk]
      simp only [compileP, obj, hyp]
      erw [ih (fun i => Presentation.rename wk (objects i))
        (Fin.cases (.var 0) (fun i => Presentation.rename wk (hyps i))) (liftSub σ)]
      cases ρ.term p <;> cases ρ.compileP ops body (fun i => Presentation.rename wk (objects i))
        (Fin.cases (.var 0) (fun i => Presentation.rename wk (hyps i))) <;> rfl
  | impE function argument ihf iha =>
      simp only [compileP, ihf, iha]
      cases ρ.compileP ops function objects hyps <;>
        cases ρ.compileP ops argument objects hyps <;> rfl
  | @allI Γ Δ τ φ body ih =>
      have hyp : (fun i : Fin (HOL.weakenHyps (σ := τ) Δ).length => Presentation.rename wk
            (Presentation.subst σ (hyps (i.cast (by simp [HOL.weakenHyps]))))) =
          (fun i => Presentation.subst (liftSub σ)
            (Presentation.rename wk (hyps (i.cast (by simp [HOL.weakenHyps]))))) := by
        funext i
        simp only [subst_liftSub_wk]
      simp only [compileP, liftSub_comp, hyp]
      erw [ih (liftSub objects)
        (fun i => Presentation.rename wk (hyps (i.cast (by simp [HOL.weakenHyps])))) (liftSub σ)]
      cases ρ.compileP ops body (liftSub objects)
        (fun i => Presentation.rename wk (hyps (i.cast (by simp [HOL.weakenHyps])))) <;> rfl
  | allE t function ih =>
      simp only [compileP, ih]
      cases ρ.term t with
      | none => rfl
      | some code =>
          cases ρ.compileP ops function objects hyps with
          | none => rfl
          | some native => simp [Presentation.subst, subst_comp]
  | eqRefl t =>
      simp only [compileP]
      cases ρ.term t with
      | none => rfl
      | some code =>
          simp only [Option.bind_eq_bind, Option.bind_some, subst_comp_apply]
          exact natural.pointed σ _ _
  | eqSymm proof ih =>
      simp only [compileP, ih]
      cases ρ.term _ <;> cases ρ.term _ <;> cases ρ.compileP ops proof objects hyps <;>
        first
          | rfl
          | (simp only [Option.bind_eq_bind, Option.bind_some, Option.map_some,
              subst_comp_apply]; exact natural.symmetry σ _ _ _ _)
  | eqTrans first second ihFirst ihSecond =>
      simp only [compileP, ihFirst, ihSecond]
      cases ρ.term _ <;> cases ρ.term _ <;> cases ρ.term _ <;>
        cases ρ.compileP ops first objects hyps <;> cases ρ.compileP ops second objects hyps <;>
        first
          | rfl
          | (simp only [Option.bind_eq_bind, Option.bind_some, Option.map_some,
              subst_comp_apply]; exact natural.transitivity σ _ _ _ _ _ _)
  | eqPropI forward backward ihForward ihBackward =>
      simp only [compileP, ihForward, ihBackward]
      cases ρ.term _ <;> cases ρ.term _ <;>
        cases ρ.compileP ops forward objects hyps <;> cases ρ.compileP ops backward objects hyps <;>
        first
          | rfl
          | (simp only [Option.bind_eq_bind, Option.bind_some, Option.map_some,
              subst_comp_apply]; exact natural.propositionExtensionality σ _ _ _ _)
  | eqPropEL proof ih =>
      simp only [compileP, ih]
      cases ρ.term _ <;> cases ρ.term _ <;> cases ρ.compileP ops proof objects hyps <;>
        first
          | rfl
          | (simp only [Option.bind_eq_bind, Option.bind_some, Option.map_some,
              subst_comp_apply]; exact natural.propositionForward σ _ _ _)
  | eqPropER proof ih =>
      simp only [compileP, ih]
      cases ρ.term _ <;> cases ρ.term _ <;> cases ρ.compileP ops proof objects hyps <;>
        try rfl
      rename_i p q e
      simp only [Option.bind_eq_bind, Option.bind_some, Option.map_some, subst_comp_apply]
      rw [natural.symmetry σ]
      cases ops.symmetry .prop (Presentation.subst objects p) (Presentation.subst objects q) e with
      | none => rfl
      | some reversed =>
          simp only [Option.map_some, Option.bind_some]
          exact natural.propositionForward σ _ _ _
  | eqApp argument proof ih =>
      simp only [compileP, ih]
      cases ρ.term _ <;> cases ρ.term _ <;> cases ρ.term _ <;>
        cases ρ.compileP ops proof objects hyps <;>
        first
          | rfl
          | (simp only [Option.bind_eq_bind, Option.bind_some, Option.map_some,
              subst_comp_apply]; exact natural.functionCongruence σ _ _ _ _ _ _)
  | eqAppArg function proof ih =>
      simp only [compileP, ih]
      cases ρ.term _ <;> cases ρ.term _ <;> cases ρ.term _ <;>
        cases ρ.compileP ops proof objects hyps <;>
        first
          | rfl
          | (simp only [Option.bind_eq_bind, Option.bind_some, Option.map_some,
              subst_comp_apply]; exact natural.argumentCongruence σ _ _ _ _ _ _)
  | @eqLam Γ Δ s τ left right proof ih =>
      have hyp : (fun i : Fin (HOL.weakenHyps (σ := s) Δ).length => Presentation.rename wk
            (Presentation.subst σ (hyps (i.cast (by simp [HOL.weakenHyps]))))) =
          (fun i => Presentation.subst (liftSub σ)
            (Presentation.rename wk (hyps (i.cast (by simp [HOL.weakenHyps]))))) := by
        funext i
        simp only [subst_liftSub_wk]
      simp only [compileP, liftSub_comp, hyp]
      erw [ih (liftSub objects)
        (fun i => Presentation.rename wk (hyps (i.cast (by simp [HOL.weakenHyps])))) (liftSub σ)]
      cases hl : ρ.term left with
      | none => rfl
      | some l =>
          cases hr : ρ.term right with
          | none => rfl
          | some r =>
              cases he : ρ.compileP ops proof (liftSub objects)
                  (fun i => Presentation.rename wk (hyps (i.cast (by simp [HOL.weakenHyps])))) with
              | none => rfl
              | some e =>
                  simp only [Option.bind_eq_bind, Option.bind_some, Option.map_some,
                    subst_comp_apply]
                  exact natural.functionExtensionality σ s τ
                    (.lam (Presentation.subst (liftSub objects) l))
                    (.lam (Presentation.subst (liftSub objects) r)) (.lam e)
  | funExt proof ih =>
      simp only [compileP, ih]
      cases ρ.term _ <;> cases ρ.term _ <;> cases ρ.compileP ops proof objects hyps <;>
        first
          | rfl
          | (simp only [Option.bind_eq_bind, Option.bind_some, Option.map_some,
              subst_comp_apply]; exact natural.functionExtensionality σ _ _ _ _ _)
  | @beta Γ Δ s τ argument body =>
      simp only [compileP]
      cases ρ.term argument <;> cases ρ.term body <;> try rfl
      rename_i a b
      simp only [Option.bind_eq_bind, Option.bind_some, liftSub_comp, subst_comp_apply]
      exact natural.pointed σ τ (.app (.lam (Presentation.subst (liftSub objects) b))
        (Presentation.subst objects a))
  | @eta Γ Δ s τ function =>
      simp only [compileP]
      cases ρ.term function with
      | none => rfl
      | some f =>
          simp only [Option.bind_eq_bind, Option.bind_some, subst_comp_apply]
          have moved : (.lam (.app (Presentation.rename wk (Presentation.subst σ
              (Presentation.subst objects f))) (.var 0)) : Tm Head m) =
              Presentation.subst σ (.lam (.app (Presentation.rename wk
                (Presentation.subst objects f)) (.var 0))) := by
            simp only [Presentation.subst, subst_liftSub_wk]
            rfl
          rw [moved]
          exact natural.pointed σ (.arr s τ) _
  | _ => rfl

end HOLReading

end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
