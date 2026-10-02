import Mathlib.Logic.Equiv.Defs
import Mettapedia.TypeTheory.Calculi.BooleanSTLC.ObservationalEquality

/-!
# Proofs of propositions: irrelevance and propositional extensionality

Observational type theory interprets a proposition as a set of proofs and
chooses its propositional fragment so that "only from a contradiction can we
make data": the eliminators of `⊤`, conjunction and universal quantification
return proofs, never data (Altenkirch, McBride and Swierstra, PLPV 2007, §2.3).

`PropCode` codes propositions, and `PropCode.Proof` gives each code its type of
proofs, proof-relevantly: a proof of a disjunction records its side.
`InFragment` is the observational fragment: `⊤`, `⊥`, conjunction, implication,
quantification over booleans and atoms read by their truth, with no disjunction
outside the hypothesis of an implication.

* In the fragment every proof type is a subsingleton (`proof_subsingleton`), and
  for a proof type this is the same as no observer separating two proofs
  (`proofBlind_iff_subsingleton`).
* **Propositional extensionality as the identity of proof types.**  For any
  family of proof types with a unit proposition, logically equivalent codes
  have equivalent proof types exactly when every proof type is a subsingleton
  (`univalentPropExt_iff_subsingleton`).
* **Control** (`Disjunction`): the proofs `inl` and `inr` of `⊤ ∨ ⊤` are
  separated by case analysis into booleans; `⊤` and `⊤ ∨ ⊤` are logically
  equivalent, yet their proof types are not equivalent, so propositional
  extensionality fails once proofs can be inspected.
* **The calculus.**  Every proposition of the boolean calculus has a code in the
  fragment (`Tm.propCode`), with maps both ways between its truth and its proofs
  (`Tm.propBridge`); so observational equality at `prop`, logical equivalence,
  is equivalence of proof types (`obsEq_prop_iff_proofEquiv`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.BooleanSTLC

universe u v

/-! ## Codes and proofs -/

/-- Codes of propositions. -/
inductive PropCode where
  | top
  | bot
  | and (left right : PropCode)
  | imp (hypothesis conclusion : PropCode)
  | all (body : Bool → PropCode)
  | atom (truth : Prop)
  | or (left right : PropCode)

/-- The proofs of a proposition.  A proof of a disjunction records its side. -/
def PropCode.Proof : PropCode → Type
  | .top => PUnit
  | .bot => PEmpty
  | .and P Q => P.Proof × Q.Proof
  | .imp P Q => P.Proof → Q.Proof
  | .all P => (x : Bool) → (P x).Proof
  | .atom p => PLift p
  | .or P Q => P.Proof ⊕ Q.Proof

/-- The propositional fragment of observational type theory: no disjunction,
except in the hypothesis of an implication. -/
inductive PropCode.InFragment : PropCode → Prop where
  | top : InFragment .top
  | bot : InFragment .bot
  | and {P Q : PropCode} : InFragment P → InFragment Q → InFragment (.and P Q)
  | imp {P Q : PropCode} : InFragment Q → InFragment (.imp P Q)
  | all {P : Bool → PropCode} : (∀ x, InFragment (P x)) → InFragment (.all P)
  | atom (p : Prop) : InFragment (.atom p)

/-- **In the fragment, proofs are irrelevant**: every proof type is a
subsingleton. -/
theorem PropCode.proof_subsingleton {P : PropCode} (inFragment : P.InFragment) :
    Subsingleton P.Proof := by
  induction inFragment with
  | top => exact ⟨fun (_ _ : PUnit) => rfl⟩
  | bot => exact ⟨fun (a : PEmpty) => nomatch a⟩
  | and _ _ ihP ihQ =>
      exact ⟨fun a b => Prod.ext (ihP.elim a.1 b.1) (ihQ.elim a.2 b.2)⟩
  | imp _ ih => exact ⟨fun f g => funext fun x => ih.elim (f x) (g x)⟩
  | all _ ih => exact ⟨fun f g => funext fun x => (ih x).elim (f x) (g x)⟩
  | atom p => exact ⟨fun (a b : PLift p) => by cases a; cases b; rfl⟩

/-- No observer of the proofs of `P` separates two proofs. -/
def PropCode.ProofBlind (P : PropCode) : Prop :=
  ∀ (observer : P.Proof → Prop) (a b : P.Proof), observer a ↔ observer b

/-- **Observers cannot inspect proofs exactly when proofs are unique.** -/
theorem PropCode.proofBlind_iff_subsingleton (P : PropCode) :
    P.ProofBlind ↔ Subsingleton P.Proof := by
  constructor
  · intro blind
    exact ⟨fun a b => ((blind (fun x => x = a) a b).mp rfl).symm⟩
  · intro unique observer a b
    rw [unique.elim a b]

/-! ## Propositional extensionality as equivalence of proof types -/

section Generic

variable {Code : Type u} (Proof : Code → Type v)

/-- Logically equivalent codes have equivalent proof types. -/
def UnivalentPropExt : Prop :=
  ∀ P Q : Code, (Proof P → Proof Q) → (Proof Q → Proof P) → Nonempty (Proof P ≃ Proof Q)

/-- Two subsingletons with maps both ways are equivalent. -/
def equivOfMaps {X Y : Type v} [Subsingleton X] [Subsingleton Y] (f : X → Y) (g : Y → X) :
    X ≃ Y where
  toFun := f
  invFun := g
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- **Propositional extensionality holds as identity of proof types exactly
when every proof type is a subsingleton**, for a family with a unit code. -/
theorem univalentPropExt_iff_subsingleton (unitCode : Code) (unitProof : Proof unitCode)
    (unitUnique : ∀ a b : Proof unitCode, a = b) :
    UnivalentPropExt Proof ↔ ∀ P, Subsingleton (Proof P) := by
  constructor
  · intro ext P
    refine ⟨fun a b => ?_⟩
    obtain ⟨e⟩ := ext P unitCode (fun _ => unitProof) (fun _ => a)
    exact e.injective (unitUnique _ _)
  · intro unique P Q f g
    have := unique P
    have := unique Q
    exact ⟨equivOfMaps f g⟩

end Generic

/-- In the fragment, logically equivalent propositions have equivalent proof
types. -/
def PropCode.proofEquivOfMaps {P Q : PropCode} (inP : P.InFragment) (inQ : Q.InFragment)
    (f : P.Proof → Q.Proof) (g : Q.Proof → P.Proof) : P.Proof ≃ Q.Proof :=
  haveI := PropCode.proof_subsingleton inP
  haveI := PropCode.proof_subsingleton inQ
  equivOfMaps f g

/-! ## Control: an inspectable disjunction -/

namespace Disjunction

/-- `⊤ ∨ ⊤`. -/
def twoProofs : PropCode := .or .top .top

def leftProof : twoProofs.Proof := Sum.inl PUnit.unit

def rightProof : twoProofs.Proof := Sum.inr PUnit.unit

/-- A proof inspector: case analysis on a proof of a disjunction, into data. -/
def inspect : twoProofs.Proof → Bool
  | .inl _ => true
  | .inr _ => false

/-- **The inspector separates two proofs of one proposition.** -/
theorem inspect_separates : inspect leftProof ≠ inspect rightProof := Bool.noConfusion

theorem leftProof_ne_rightProof : leftProof ≠ rightProof := fun same =>
  inspect_separates (congrArg inspect same)

theorem twoProofs_not_proofBlind : ¬ twoProofs.ProofBlind := fun blind =>
  leftProof_ne_rightProof (((twoProofs.proofBlind_iff_subsingleton).mp blind).elim _ _)

/-- `⊤` and `⊤ ∨ ⊤` are logically equivalent ... -/
def topToTwo : PropCode.top.Proof → twoProofs.Proof := fun _ => leftProof

def twoToTop : twoProofs.Proof → PropCode.top.Proof := fun _ => PUnit.unit

/-- ... **but their proof types are not equivalent.** -/
theorem not_proofEquiv : ¬ Nonempty (PropCode.top.Proof ≃ twoProofs.Proof) := by
  rintro ⟨e⟩
  apply leftProof_ne_rightProof
  have left : e (e.symm leftProof) = leftProof := e.apply_symm_apply _
  have right : e (e.symm rightProof) = rightProof := e.apply_symm_apply _
  rw [← left, ← right]
  exact congrArg e (Subsingleton.elim (α := PUnit) _ _)

/-- **With proof inspection, propositional extensionality fails** as identity of
proof types. -/
theorem not_univalentPropExt : ¬ UnivalentPropExt PropCode.Proof := fun ext =>
  not_proofEquiv (ext .top twoProofs topToTwo twoToTop)

end Disjunction

/-! ## The propositions of the calculus -/

/-- The codes available at a type: a proposition code at `prop`, and nothing at
the other types. -/
def PropCodeAt : Ty → Type
  | .prop => PropCode
  | .bool => PUnit
  | .prod _ _ => PUnit
  | .arr _ _ => PUnit

/-- A value read as an atomic code, at `prop`. -/
def atomAt : (A : Ty) → A.denote → PropCodeAt A
  | .prop, p => PropCode.atom p
  | .bool, _ => PUnit.unit
  | .prod _ _, _ => PUnit.unit
  | .arr _ _, _ => PUnit.unit

/-- The code of a term in an environment: connectives are decoded, and every
other proposition is an atom read by its truth. -/
def Tm.codeAt : {Γ : Ctx} → {A : Ty} → Tm Γ A → Env Γ → PropCodeAt A
  | _, _, .top, _ => PropCode.top
  | _, _, .bot, _ => PropCode.bot
  | _, _, .and p q, γ => PropCode.and (p.codeAt γ) (q.codeAt γ)
  | _, _, .imp p q, γ => PropCode.imp (p.codeAt γ) (q.codeAt γ)
  | _, _, .allBool b, γ => PropCode.all fun x => b.codeAt (γ.cons x)
  | _, A, t, γ => atomAt A (t.eval γ)

/-- The code of a proposition of the calculus in an environment. -/
def Tm.propCode {Γ : Ctx} (t : Tm Γ .prop) (γ : Env Γ) : PropCode :=
  t.codeAt γ

theorem Tm.propCode_inFragment : {Γ : Ctx} → (t : Tm Γ .prop) → (γ : Env Γ) →
    (t.propCode γ).InFragment
  | _, .top, _ => .top
  | _, .bot, _ => .bot
  | _, .and p q, γ => .and (p.propCode_inFragment γ) (q.propCode_inFragment γ)
  | _, .imp _ q, γ => .imp (q.propCode_inFragment γ)
  | _, .allBool b, γ => .all fun x => b.propCode_inFragment (γ.cons x)
  | _, .isTrue _, _ => .atom _
  | _, .var _, _ => .atom _
  | _, .ite _ _ _, _ => .atom _
  | _, .fst _, _ => .atom _
  | _, .snd _, _ => .atom _
  | _, .app _ _, _ => .atom _

/-- Maps both ways between the truth of a proposition and a type of proofs. -/
structure TruthProofs (truth : Prop) (Proof : Type) where
  prove : truth → Proof
  sound : Proof → truth

/-- **Truth and proofs, both ways**: every true proposition of the calculus has a
proof of its code, and every proof of its code makes it true. -/
def Tm.propBridge : {Γ : Ctx} → (t : Tm Γ .prop) → (γ : Env Γ) →
    TruthProofs (t.eval γ) (t.propCode γ).Proof
  | _, .top, _ => ⟨fun _ => PUnit.unit, fun _ => trivial⟩
  | _, .bot, _ => ⟨fun h => h.elim, fun h => nomatch h⟩
  | _, .and p q, γ =>
      ⟨fun h => ((p.propBridge γ).prove h.1, (q.propBridge γ).prove h.2),
        fun h => ⟨(p.propBridge γ).sound h.1, (q.propBridge γ).sound h.2⟩⟩
  | _, .imp p q, γ =>
      ⟨fun h proofP => (q.propBridge γ).prove (h ((p.propBridge γ).sound proofP)),
        fun h truthP => (q.propBridge γ).sound (h ((p.propBridge γ).prove truthP))⟩
  | _, .allBool b, γ =>
      ⟨fun h x => (b.propBridge (γ.cons x)).prove (h x),
        fun h x => (b.propBridge (γ.cons x)).sound (h x)⟩
  | _, .isTrue _, _ => ⟨PLift.up, PLift.down⟩
  | _, .var _, _ => ⟨PLift.up, PLift.down⟩
  | _, .ite _ _ _, _ => ⟨PLift.up, PLift.down⟩
  | _, .fst _, _ => ⟨PLift.up, PLift.down⟩
  | _, .snd _, _ => ⟨PLift.up, PLift.down⟩
  | _, .app _ _, _ => ⟨PLift.up, PLift.down⟩

theorem Tm.eval_iff_nonempty_proof {Γ : Ctx} (t : Tm Γ .prop) (γ : Env Γ) :
    t.eval γ ↔ Nonempty (t.propCode γ).Proof :=
  ⟨fun h => ⟨(t.propBridge γ).prove h⟩, fun ⟨proof⟩ => (t.propBridge γ).sound proof⟩

/-- **At `prop`, observational equality is equivalence of proof types.**  The
propositions of the calculus lie in the irrelevant fragment, so logical
equivalence and the identity of proof types coincide. -/
theorem obsEq_prop_iff_proofEquiv (t u : Closed .prop) :
    ObsEq .prop t u ↔
      Nonempty ((t.propCode Env.empty).Proof ≃ (u.propCode Env.empty).Proof) := by
  constructor
  · intro related
    exact ⟨PropCode.proofEquivOfMaps (t.propCode_inFragment _) (u.propCode_inFragment _)
      (fun proof => (u.propBridge _).prove (related.mp ((t.propBridge _).sound proof)))
      (fun proof => (t.propBridge _).prove (related.mpr ((u.propBridge _).sound proof)))⟩
  · rintro ⟨e⟩
    exact ⟨fun truth => (u.propBridge _).sound (e ((t.propBridge _).prove truth)),
      fun truth => (t.propBridge _).sound (e.symm ((u.propBridge _).prove truth))⟩

end Mettapedia.TypeTheory.Calculi.BooleanSTLC
