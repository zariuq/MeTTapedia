import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.RecursionEquations
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.TelescopeAbstractions

/-!
# Definitions by structural recursion with later arguments on the left

A function of several arguments that recurses on its first one is written with all its
arguments on the left of its equations:

    append nil ys ⟶ ys
    append (cons a as) ys ⟶ cons a (append as ys)

`RecursionEquations.lean` gives the form in which the later arguments are part of the result
family and the right sides take them by abstraction. This module gives the written form and
relates the two.

**Telescopes under substitution.** The later arguments are a telescope (`CTele`) over the
inspected argument. A substitution acts on a telescope entry by entry, lifted under the
entries before (`CTele.subst`, `CTele.liftAlong`; `CTele.endAt` is the number of variables
the result ends at). The function type and the abstraction over a telescope commute with it
(`CTele.pis_subst`, `CTele.lams_subst`). Over a formed extension of a context, the function
type over the telescope is a type (`CTele.pis_formed`) and the abstraction of a typed term has
it (`CTele.lams_typed`).

**The written equations** (`laterEquation`, `laterEquations`). Let `Ξ` be the telescope of
the later arguments over the inspected argument and `C` the result type over all of them; the
result family is `Ξ.pis C`. For a constructor, a right side is a body over the fields, the
hypotheses for the recursive fields, and the later arguments at the constructor form
(`laterTele`); a hypothesis is the function at a recursive field, to be applied to later
arguments of the body's choice. The equation has, on the left, the defined constant at the
constructor form applied to the variables of the later arguments (`CTele.etaBody`), and on the
right the body with the recursive calls in place of the hypotheses; its telescope is the
fields followed by the later arguments.

**The abstracted form** (`abstractedBody`): the body abstracted over the later arguments is a
right side in the sense of `RecursionEquations.lean`, typed at the result family at the
constructor form when the body is typed (`abstractedBody_typed`).

The set model of the written equations is in `TowerInterpretation/SetLaterArguments.lean`.

Positive example: with no later argument the telescope is empty, the abstracted body is the
body, and the written equation is the equation of `RecursionEquations.lean`
(`laterEquation_nil`). Negative example: the substitution of a telescope keeps its length, so
a function declared with one later argument has no equation with two
(`CTele.endAt_cons_nil`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Normalization
open UniverseLevel (LevelOrder)

variable {Head : Type}

/-! ## Telescopes under substitution -/

namespace CTele

/-- The number of variables a telescope ends at, when it starts at `k` variables. -/
def endAt : {n m : Nat} → CTele Head n m → Nat → Nat
  | _, _, .nil, k => k
  | _, _, .cons _ rest, k => endAt rest (k + 1)

/-- A substitution lifted under the entries of a telescope. -/
def liftAlong : {n m : Nat} → (tele : CTele Head n m) → {k : Nat} → CSub Head n k →
    CSub Head m (tele.endAt k)
  | _, _, .nil, _, σ => σ
  | _, _, .cons _ rest, _, σ => liftAlong rest (CTm.liftSub σ)

/-- **A telescope under a substitution**: each entry substituted, under the entries before
it. -/
def subst : {n m : Nat} → (tele : CTele Head n m) → {k : Nat} → CSub Head n k →
    CTele Head k (tele.endAt k)
  | _, _, .nil, _, _ => .nil
  | _, _, .cons A rest, _, σ => .cons (A.subst σ) (subst rest (CTm.liftSub σ))

/-- Negative example: a telescope of one entry ends one variable after its start, whatever is
substituted. -/
theorem endAt_cons_nil {n : Nat} (A : CTm Head n) (k : Nat) :
    (CTele.cons A .nil).endAt k = k + 1 := rfl

/-- The function type over a telescope, under a substitution. -/
theorem pis_subst : ∀ {n m : Nat} (tele : CTele Head n m) (T : CTm Head m) {k : Nat}
    (σ : CSub Head n k),
    (tele.pis T).subst σ = (tele.subst σ).pis (T.subst (tele.liftAlong σ))
  | _, _, .nil, _, _, _ => rfl
  | _, _, .cons A rest, T, _, σ => by
      show CTm.pi (A.subst σ) ((rest.pis T).subst (CTm.liftSub σ)) =
        .pi (A.subst σ) ((rest.subst (CTm.liftSub σ)).pis
          (T.subst (rest.liftAlong (CTm.liftSub σ))))
      rw [pis_subst rest T (CTm.liftSub σ)]

/-- The abstraction over a telescope, under a substitution. -/
theorem lams_subst : ∀ {n m : Nat} (tele : CTele Head n m) (b : CTm Head m) {k : Nat}
    (σ : CSub Head n k),
    (tele.lams b).subst σ = (tele.subst σ).lams (b.subst (tele.liftAlong σ))
  | _, _, .nil, _, _, _ => rfl
  | _, _, .cons A rest, b, _, σ => by
      show CTm.lam (A.subst σ) ((rest.lams b).subst (CTm.liftSub σ)) =
        .lam (A.subst σ) ((rest.subst (CTm.liftSub σ)).lams
          (b.subst (rest.liftAlong (CTm.liftSub σ))))
      rw [lams_subst rest b (CTm.liftSub σ)]

section Judgment

variable {L : Type} [LevelOrder L] {R : Rules Head} {Q : ChurchRules R}

/-- The context a formed extension extends is formed. -/
theorem formed_of_extend : ∀ {n m : Nat} (tele : CTele Head n m) {Γ : CCtx Head n},
    CCtxFormed Q (tele.extend Γ) → CCtxFormed Q Γ
  | _, _, .nil, _, formed => formed
  | _, _, .cons A rest, Γ, formed => by
      have inner : CCtxFormed Q (Γ.snoc A) := formed_of_extend rest formed
      cases inner with
      | snoc formedΓ _ => exact formedΓ

/-- **The function type over a telescope of a type over it is a type**, when the extended
context is formed. -/
theorem pis_formed (levels : LevelModel R L) : ∀ {n m : Nat} (tele : CTele Head n m)
    {Γ : CCtx Head n} {C : CTm Head m}, CCtxFormed Q (tele.extend Γ) →
      CIsType Q (tele.extend Γ) C → CIsType Q Γ (tele.pis C)
  | _, _, .nil, _, _, _, typeC => typeC
  | _, _, .cons A rest, Γ, C, formed, typeC => by
      have inner : CCtxFormed Q (Γ.snoc A) := formed_of_extend rest formed
      cases inner with
      | snoc _ typeA => exact CIsType.pi levels typeA (pis_formed levels rest formed typeC)

/-- **The abstraction over a telescope of a typed term has the function type over the
telescope**, when the extended context is formed. -/
theorem lams_typed (levels : LevelModel R L) : ∀ {n m : Nat} (tele : CTele Head n m)
    {Γ : CCtx Head n} {b C : CTm Head m}, CCtxFormed Q (tele.extend Γ) →
      CIsType Q (tele.extend Γ) C → CTyped Q (tele.extend Γ) b C →
        CTyped Q Γ (tele.lams b) (tele.pis C)
  | _, _, .nil, _, _, _, _, _, typed => typed
  | _, _, .cons A rest, Γ, b, C, formed, typeC, typed => by
      have inner : CCtxFormed Q (Γ.snoc A) := formed_of_extend rest formed
      have codomain := pis_formed levels rest formed typeC
      have body := lams_typed levels rest formed typeC typed
      cases inner with
      | snoc _ typeA =>
        obtain ⟨c, hc, piTyped⟩ := CIsType.pi levels typeA codomain
        obtain ⟨w, hw, typedA⟩ := typeA
        exact .lamIntro typedA hw piTyped hc body

end Judgment

end CTele

/-! ## The written equations -/

section Equations

variable {m : Nat} (f T : DeclName) (Ξ : CTele Head 1 m) (C : CTm Head m)

/-- The later arguments in the context of a method of constructor `k`, at the constructor
form. -/
def laterTele (k : DeclName) (fields : List (Field Head)) :
    CTele Head (fields.length + (recPositions fields).length)
      (Ξ.endAt (fields.length + (recPositions fields).length)) :=
  Ξ.subst fun _ => ctorAt k fields.length (recPositions fields).length

/-- The result type in the context of a body of constructor `k`. -/
def laterResult (k : DeclName) (fields : List (Field Head)) :
    CTm Head (Ξ.endAt (fields.length + (recPositions fields).length)) :=
  C.subst (Ξ.liftAlong fun _ => ctorAt k fields.length (recPositions fields).length)

/-- The context of a body of constructor `k`: the fields, the hypotheses for the recursive
fields, and the later arguments at the constructor form. -/
def laterCtx (k : DeclName) (fields : List (Field Head)) :
    CCtx Head (Ξ.endAt (fields.length + (recPositions fields).length)) :=
  (laterTele Ξ k fields).extend
    (methodCtx T (Ξ.pis C) fields (recPositions fields).length)

/-- **The body abstracted over the later arguments**: a right side in the form of
`RecursionEquations.lean`. -/
def abstractedBody (k : DeclName) (fields : List (Field Head))
    (body : CTm Head (Ξ.endAt (fields.length + (recPositions fields).length))) :
    CTm Head (fields.length + (recPositions fields).length) :=
  (laterTele Ξ k fields).lams body

/-- The later arguments in the telescope of the written equation of constructor `k`. -/
def writtenTele (k : DeclName) (fields : List (Field Head)) :
    CTele Head fields.length ((laterTele Ξ k fields).endAt fields.length) :=
  (laterTele Ξ k fields).subst (callSub f fields)

/-- **The written equation of a constructor**: over the fields and the later arguments, the
defined constant at the constructor form applied to the later arguments, and the body with
the recursive calls in place of the hypotheses. -/
def laterEquation (k : DeclName) (fields : List (Field Head))
    (body : CTm Head (Ξ.endAt (fields.length + (recPositions fields).length))) :
    DefiningEquation Head where
  arity := (laterTele Ξ k fields).endAt fields.length
  telescope := (writtenTele f Ξ k fields).extend (liftCtx (ctorTele T fields))
  left := (writtenTele f Ξ k fields).etaBody
    (.app (.const f) (liftTm (appSpine (.const k) (metaVars fields.length))))
  right := body.subst ((laterTele Ξ k fields).liftAlong (callSub f fields))

/-- **The written equations of a definition by structural recursion**, one for each
constructor. -/
def laterEquations (ctors : List (DeclName × List (Field Head)))
    (body : (k : DeclName) → (fields : List (Field Head)) →
      CTm Head (Ξ.endAt (fields.length + (recPositions fields).length))) :
    List (DefiningEquation Head) :=
  ctors.map fun entry => laterEquation f T Ξ entry.1 entry.2 (body entry.1 entry.2)

variable {f T Ξ C}

/-- A written equation of the definition is the written equation of one of the
constructors. -/
theorem mem_laterEquations {ctors : List (DeclName × List (Field Head))}
    {body : (k : DeclName) → (fields : List (Field Head)) →
      CTm Head (Ξ.endAt (fields.length + (recPositions fields).length))}
    {e : DefiningEquation Head} (member : e ∈ laterEquations f T Ξ ctors body) :
    ∃ (i : Nat) (k : DeclName) (fields : List (Field Head)), ctors[i]? = some (k, fields) ∧
      e = laterEquation f T Ξ k fields (body k fields) := by
  obtain ⟨entry, memberEntry, rfl⟩ := List.mem_map.mp member
  obtain ⟨i, found⟩ := List.getElem?_of_mem memberEntry
  exact ⟨i, entry.1, entry.2, found, rfl⟩

/-- **The abstracted body is typed** at the result family at the constructor form, when the
body is typed in its context, the context is formed and the result type is a type there. -/
theorem abstractedBody_typed {L : Type} [LevelOrder L] {R : Rules Head} {Q : ChurchRules R}
    (levels : LevelModel R L) {k : DeclName} {fields : List (Field Head)}
    {body : CTm Head (Ξ.endAt (fields.length + (recPositions fields).length))}
    (formed : CCtxFormed Q (laterCtx T Ξ C k fields))
    (resultType : CIsType Q (laterCtx T Ξ C k fields) (laterResult Ξ C k fields))
    (typed : CTyped Q (laterCtx T Ξ C k fields) body (laterResult Ξ C k fields)) :
    CTyped Q (methodCtx T (Ξ.pis C) fields (recPositions fields).length)
      (abstractedBody Ξ k fields body)
      ((Ξ.pis C).subst fun _ => ctorAt k fields.length (recPositions fields).length) := by
  rw [CTele.pis_subst]
  exact CTele.lams_typed levels (laterTele Ξ k fields) formed resultType typed

end Equations

/-- Positive example: with no later argument the written equation is the equation of
`RecursionEquations.lean`. -/
theorem laterEquation_nil (f T k : DeclName) (fields : List (Field Head))
    (body : CTm Head (fields.length + (recPositions fields).length)) :
    laterEquation f T (CTele.nil : CTele Head 1 1) k fields body =
      recursionEquation f T k fields body := rfl

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
