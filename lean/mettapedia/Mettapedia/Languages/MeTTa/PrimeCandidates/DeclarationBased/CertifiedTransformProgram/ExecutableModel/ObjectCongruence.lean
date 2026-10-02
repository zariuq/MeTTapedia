import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectFormation

/-!
# Congruence, symmetry and transitivity of identity proofs in the object package

The object package has the identity eliminator `id:eliminate` as a declared constant. This
module derives from it the congruence of identity proofs under a function: from a proof that
`x` and `y` are identical in `A`, and a function `f` from `A` to `B`, a proof that `f x` and
`f y` are identical in `B`. Nothing is added to the judgment: the proof is a term. Symmetry
(`sym_typed`: from `Id A x y`, a proof of `Id A y x`) and transitivity (`trans_typed`: from
`Id A x y` and `Id A y z`, a proof of `Id A x z`) are derived the same way, each over the
context of its data (`symTerm_typed`, `transTerm_typed`).

The derivation is made once, over the context of its data, where every instantiation is a
computation on variables: two types `A` and `B` of the lowest universe, a function, two terms
and an identity proof (`congCtx`). The term (`congTerm`) is the eliminator at the motive
"`f x` is identical to `f y'`" (`congMotive`), at reflexivity of `f x`, and at the proof. Its
typing (`congTerm_typed`) uses the motive at a term and a proof twice, each time reduced by
two β-steps (`congMotive_at`): once at `x` and reflexivity, for the base, and once at `y` and
the proof, for the result.

Every instance follows by substituting typed terms for the six variables
(`CTyped.substitute`), in the object package (`cong_typed`) and in every package that contains
it.

Positive example: from an identity proof between two numbers, an identity proof between their
successors (`cong_suc`). The function of the congruence has one type for all its values; a
function whose result type depends on its argument is not covered, and needs the eliminator at
a motive of its own.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Annotated
open Package (jName jType)

namespace CodeModel

/-! ## Congruence of identity proofs, from the identity eliminator -/

/-- The context of two types of the lowest universe, a function between them, two terms of
the first and an identity proof between these. -/
abbrev congCtx : CCtx Tower.Head 6 :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil cU0) cU0) (.pi (.var 1) (.var 1))) (.var 2))
    (.var 3)) (.id (.var 4) (.var 1) (.var 0))

/-- The motive of the congruence over that context: for `y'` and an identity proof of `x`
and `y'`, the identity type of `f x` and `f y'`. -/
abbrev congMotive : CTm Tower.Head 6 :=
  .lam (.var 5) (.lam (.id (.var 6) (.var 3) (.var 0))
    (.id (.var 6) (.app (.var 5) (.var 4)) (.app (.var 5) (.var 1))))

/-- The congruence term over that context: the identity eliminator at the motive, at
reflexivity of `f x`, and at the proof. -/
abbrev congTerm : CTm Tower.Head 6 :=
  .app (.app (.app (.app (.app (.app (.const jName) (.var 5)) (.var 2)) congMotive)
    (.refl (.app (.var 3) (.var 2)))) (.var 1)) (.var 0)

theorem congMotive_inner_typed :
    CTyped objectChurch (.snoc congCtx (.var 5))
      (.lam (.id (.var 6) (.var 3) (.var 0))
        (.id (.var 6) (.app (.var 5) (.var 4)) (.app (.var 5) (.var 1))))
      (.pi (.id (.var 6) (.var 3) (.var 0)) cU0) := by
  have domain : CTyped objectChurch (.snoc congCtx (.var 5)) (.id (.var 6) (.var 3) (.var 0)) cU0 :=
    cidT (.var 6) (.var 3) (.var 0)
  have body : CTyped objectChurch (.snoc (.snoc congCtx (.var 5)) (.id (.var 6) (.var 3) (.var 0)))
      (.id (.var 6) (.app (.var 5) (.var 4)) (.app (.var 5) (.var 1))) cU0 :=
    cidT (.var 6) (.appElim (B := .var 7) (.var 5) (.var 4))
      (.appElim (B := .var 7) (.var 5) (.var 1))
  exact .lamIntro domain (.sort _) (cpiT (craise domain) cU0_typed) (.sort _) body

theorem congMotiveType_formed :
    CTyped objectChurch congCtx (.pi (.var 5) (.pi (.id (.var 6) (.var 3) (.var 0)) cU0)) cU1 :=
  cpiT (craise (.var 5)) (cpiT (craise (cidT (.var 6) (.var 3) (.var 0))) cU0_typed)

theorem congMotive_typed :
    CTyped objectChurch congCtx congMotive
      (.pi (.var 5) (.pi (.id (.var 6) (.var 3) (.var 0)) cU0)) :=
  .lamIntro (.var 5) (.sort _) congMotiveType_formed (.sort _) congMotive_inner_typed

/-- **The motive at a term and an identity proof** is the identity type of `f x` and `f` at
the term: two β-steps. -/
theorem congMotive_at {a q : CTm Tower.Head 6} (ha : CTyped objectChurch congCtx a (.var 5))
    (hq : CTyped objectChurch congCtx q (.id (.var 5) (.var 2) a)) :
    CEqual objectChurch congCtx (.app (.app congMotive a) q)
      (.id (.var 4) (.app (.var 3) (.var 2)) (.app (.var 3) a)) cU0 := by
  have beta₁ : CEqual objectChurch congCtx (.app congMotive a)
      (.lam (.id (.var 5) (.var 2) a)
        (.id (.var 5) (.app (.var 4) (.var 3)) (.app (.var 4) (a.rename wk))))
      (.pi (.id (.var 5) (.var 2) a) cU0) :=
    .betaPi (A := .var 5) (B := .pi (.id (.var 6) (.var 3) (.var 0)) cU0)
      (body := .lam (.id (.var 6) (.var 3) (.var 0))
        (.id (.var 6) (.app (.var 5) (.var 4)) (.app (.var 5) (.var 1))))
      (a := a) congMotiveType_formed (.sort _) congMotive_inner_typed ha
  have domain : CTyped objectChurch congCtx (.id (.var 5) (.var 2) a) cU0 :=
    cidT (.var 5) (.var 2) ha
  have body : CTyped objectChurch (.snoc congCtx (.id (.var 5) (.var 2) a))
      (.id (.var 5) (.app (.var 4) (.var 3)) (.app (.var 4) (a.rename wk))) cU0 :=
    cidT (.var 5) (.appElim (B := .var 6) (.var 4) (.var 3))
      (.appElim (B := .var 6) (.var 4) (CTyped.weaken ha))
  have beta₂ : CEqual objectChurch congCtx
      (.app (.lam (.id (.var 5) (.var 2) a)
        (.id (.var 5) (.app (.var 4) (.var 3)) (.app (.var 4) (a.rename wk)))) q)
      (.id (.var 4) (.app (.var 3) (.var 2)) (.app (.var 3) (CTm.inst0 q (a.rename wk)))) cU0 :=
    .betaPi (A := .id (.var 5) (.var 2) a) (B := cU0)
      (body := .id (.var 5) (.app (.var 4) (.var 3)) (.app (.var 4) (a.rename wk))) (a := q)
      (cpiT (craise domain) cU0_typed) (.sort _) body hq
  rw [CTm.inst0_rename_wk] at beta₂
  exact .trans (.appCong (B := cU0) beta₁ (.refl hq)) beta₂

/-- **Congruence from the identity eliminator**, over the context of its data: the term is an
identity proof of `f x` and `f y`. -/
theorem congTerm_typed :
    CTyped objectChurch congCtx congTerm
      (.id (.var 4) (.app (.var 3) (.var 2)) (.app (.var 3) (.var 1))) := by
  have eliminator : CTyped objectChurch congCtx (.const jName)
      (.pi cU0 (.pi (.var 0)
        (.pi (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) cU0))
          (.pi (.app (.app (.var 0) (.var 1)) (.refl (.var 1)))
            (.pi (.var 3) (.pi (.id (.var 4) (.var 3) (.var 0))
              (.app (.app (.var 3) (.var 1)) (.var 0)))))))) := cj_typed
  have atType := CDerivable.appElim eliminator (CDerivable.var (Γ := congCtx) 5)
  have atLeft := CDerivable.appElim atType (CDerivable.var (Γ := congCtx) 2)
  have atMotive := CDerivable.appElim atLeft congMotive_typed
  have image : CTyped objectChurch congCtx (.app (.var 3) (.var 2)) (.var 4) :=
    .appElim (B := .var 5) (.var 3) (.var 2)
  have base : CTyped objectChurch congCtx (.refl (.app (.var 3) (.var 2)))
      (.app (.app congMotive (.var 2)) (.refl (.var 2))) :=
    .conv (.reflIntro image) (.symm (congMotive_at (.var 2) (.reflIntro (.var 2)))) (.sort _)
  have atBase := CDerivable.appElim atMotive base
  have atRight := CDerivable.appElim atBase (CDerivable.var (Γ := congCtx) 1)
  have atProof := CDerivable.appElim atRight (CDerivable.var (Γ := congCtx) 0)
  exact .conv atProof (congMotive_at (.var 1) (.var 0)) (.sort _)

/-- The instance of the congruence term at given data. -/
abbrev congOf {n : Nat} (A B f x y p : CTm Tower.Head n) : CTm Tower.Head n :=
  congTerm.subst fun i => [p, y, x, f, B, A].getD i.val A

/-- **Congruence of identity proofs**: for two types of the lowest universe, a function between
them, and an identity proof of two terms of the first, the congruence term is an identity proof
of the two values of the function. -/
theorem cong_typed {n : Nat} {Γ : CCtx Tower.Head n} {A B f x y p : CTm Tower.Head n}
    (hA : CTyped objectChurch Γ A cU0) (hB : CTyped objectChurch Γ B cU0)
    (hf : CTyped objectChurch Γ f (.pi A (B.rename wk))) (hx : CTyped objectChurch Γ x A)
    (hy : CTyped objectChurch Γ y A) (hp : CTyped objectChurch Γ p (.id A x y)) :
    CTyped objectChurch Γ (congOf A B f x y p) (.id B (.app f x) (.app f y)) :=
  congTerm_typed.substitute (σ := fun i => [p, y, x, f, B, A].getD i.val A)
    (fun j => match j with
      | ⟨0, _⟩ => hp
      | ⟨1, _⟩ => hy
      | ⟨2, _⟩ => hx
      | ⟨3, _⟩ => hf
      | ⟨4, _⟩ => hB
      | ⟨5, _⟩ => hA)

/-- Positive: from an identity proof between two numbers, an identity proof between their
successors. -/
theorem cong_suc {n : Nat} {Γ : CCtx Tower.Head n} {a b p : CTm Tower.Head n}
    (ha : CTyped objectChurch Γ a cnum) (hb : CTyped objectChurch Γ b cnum)
    (hp : CTyped objectChurch Γ p (.id cnum a b)) :
    CTyped objectChurch Γ (congOf cnum cnum (.const sucN) a b p) (.id cnum (csuc a) (csuc b)) :=
  cong_typed cnum_typed cnum_typed csucConst_typed ha hb hp

/-! ## Symmetry of identity proofs -/

/-- The context of a type of the lowest universe, two terms of it and an identity proof
between them. -/
abbrev symCtx : CCtx Tower.Head 4 :=
  .snoc (.snoc (.snoc (.snoc .nil cU0) (.var 0)) (.var 1)) (.id (.var 2) (.var 1) (.var 0))

/-- The motive of symmetry: for `y'` and an identity proof of `x` and `y'`, the identity type
of `y'` and `x`. -/
abbrev symMotive : CTm Tower.Head 4 :=
  .lam (.var 3) (.lam (.id (.var 4) (.var 3) (.var 0)) (.id (.var 5) (.var 1) (.var 4)))

/-- The symmetry term: the identity eliminator at the motive, at reflexivity of `x`, and at
the proof. -/
abbrev symTerm : CTm Tower.Head 4 :=
  .app (.app (.app (.app (.app (.app (.const jName) (.var 3)) (.var 2)) symMotive)
    (.refl (.var 2))) (.var 1)) (.var 0)

theorem symMotive_inner_typed :
    CTyped objectChurch (.snoc symCtx (.var 3))
      (.lam (.id (.var 4) (.var 3) (.var 0)) (.id (.var 5) (.var 1) (.var 4)))
      (.pi (.id (.var 4) (.var 3) (.var 0)) cU0) := by
  have domain : CTyped objectChurch (.snoc symCtx (.var 3)) (.id (.var 4) (.var 3) (.var 0))
      cU0 := cidT (.var 4) (.var 3) (.var 0)
  have body : CTyped objectChurch (.snoc (.snoc symCtx (.var 3)) (.id (.var 4) (.var 3) (.var 0)))
      (.id (.var 5) (.var 1) (.var 4)) cU0 := cidT (.var 5) (.var 1) (.var 4)
  exact .lamIntro domain (.sort _) (cpiT (craise domain) cU0_typed) (.sort _) body

theorem symMotiveType_formed :
    CTyped objectChurch symCtx (.pi (.var 3) (.pi (.id (.var 4) (.var 3) (.var 0)) cU0)) cU1 :=
  cpiT (craise (.var 3)) (cpiT (craise (cidT (.var 4) (.var 3) (.var 0))) cU0_typed)

theorem symMotive_typed :
    CTyped objectChurch symCtx symMotive
      (.pi (.var 3) (.pi (.id (.var 4) (.var 3) (.var 0)) cU0)) :=
  .lamIntro (.var 3) (.sort _) symMotiveType_formed (.sort _) symMotive_inner_typed

/-- The motive of symmetry at a term and an identity proof: two β-steps. -/
theorem symMotive_at {a q : CTm Tower.Head 4} (ha : CTyped objectChurch symCtx a (.var 3))
    (hq : CTyped objectChurch symCtx q (.id (.var 3) (.var 2) a)) :
    CEqual objectChurch symCtx (.app (.app symMotive a) q) (.id (.var 3) a (.var 2)) cU0 := by
  have beta₁ : CEqual objectChurch symCtx (.app symMotive a)
      (.lam (.id (.var 3) (.var 2) a) (.id (.var 4) (a.rename wk) (.var 3)))
      (.pi (.id (.var 3) (.var 2) a) cU0) :=
    .betaPi (A := .var 3) (B := .pi (.id (.var 4) (.var 3) (.var 0)) cU0)
      (body := .lam (.id (.var 4) (.var 3) (.var 0)) (.id (.var 5) (.var 1) (.var 4)))
      (a := a) symMotiveType_formed (.sort _) symMotive_inner_typed ha
  have domain : CTyped objectChurch symCtx (.id (.var 3) (.var 2) a) cU0 :=
    cidT (.var 3) (.var 2) ha
  have body : CTyped objectChurch (.snoc symCtx (.id (.var 3) (.var 2) a))
      (.id (.var 4) (a.rename wk) (.var 3)) cU0 :=
    cidT (.var 4) (CTyped.weaken ha) (.var 3)
  have beta₂ : CEqual objectChurch symCtx
      (.app (.lam (.id (.var 3) (.var 2) a) (.id (.var 4) (a.rename wk) (.var 3))) q)
      (.id (.var 3) (CTm.inst0 q (a.rename wk)) (.var 2)) cU0 :=
    .betaPi (A := .id (.var 3) (.var 2) a) (B := cU0)
      (body := .id (.var 4) (a.rename wk) (.var 3)) (a := q)
      (cpiT (craise domain) cU0_typed) (.sort _) body hq
  rw [CTm.inst0_rename_wk] at beta₂
  exact .trans (.appCong (B := cU0) beta₁ (.refl hq)) beta₂

/-- **Symmetry from the identity eliminator**, over the context of its data. -/
theorem symTerm_typed : CTyped objectChurch symCtx symTerm (.id (.var 3) (.var 1) (.var 2)) := by
  have eliminator : CTyped objectChurch symCtx (.const jName)
      (.pi cU0 (.pi (.var 0)
        (.pi (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) cU0))
          (.pi (.app (.app (.var 0) (.var 1)) (.refl (.var 1)))
            (.pi (.var 3) (.pi (.id (.var 4) (.var 3) (.var 0))
              (.app (.app (.var 3) (.var 1)) (.var 0)))))))) := cj_typed
  have atType := CDerivable.appElim eliminator (CDerivable.var (Γ := symCtx) 3)
  have atLeft := CDerivable.appElim atType (CDerivable.var (Γ := symCtx) 2)
  have atMotive := CDerivable.appElim atLeft symMotive_typed
  have base : CTyped objectChurch symCtx (.refl (.var 2))
      (.app (.app symMotive (.var 2)) (.refl (.var 2))) :=
    .conv (.reflIntro (.var 2)) (.symm (symMotive_at (.var 2) (.reflIntro (.var 2)))) (.sort _)
  have atBase := CDerivable.appElim atMotive base
  have atRight := CDerivable.appElim atBase (CDerivable.var (Γ := symCtx) 1)
  have atProof := CDerivable.appElim atRight (CDerivable.var (Γ := symCtx) 0)
  exact .conv atProof (symMotive_at (.var 1) (.var 0)) (.sort _)

/-- The instance of the symmetry term at given data. -/
abbrev symOf {n : Nat} (A x y p : CTm Tower.Head n) : CTm Tower.Head n :=
  symTerm.subst fun i => [p, y, x, A].getD i.val A

/-- **Symmetry of identity proofs.** -/
theorem sym_typed {n : Nat} {Γ : CCtx Tower.Head n} {A x y p : CTm Tower.Head n}
    (hA : CTyped objectChurch Γ A cU0) (hx : CTyped objectChurch Γ x A)
    (hy : CTyped objectChurch Γ y A) (hp : CTyped objectChurch Γ p (.id A x y)) :
    CTyped objectChurch Γ (symOf A x y p) (.id A y x) :=
  symTerm_typed.substitute (σ := fun i => [p, y, x, A].getD i.val A)
    (fun j => match j with
      | ⟨0, _⟩ => hp
      | ⟨1, _⟩ => hy
      | ⟨2, _⟩ => hx
      | ⟨3, _⟩ => hA)

/-! ## Transitivity of identity proofs -/

/-- The context of a type of the lowest universe, three terms of it and identity proofs
between the first two and the last two. -/
abbrev transCtx : CCtx Tower.Head 6 :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil cU0) (.var 0)) (.var 1)) (.var 2))
    (.id (.var 3) (.var 2) (.var 1))) (.id (.var 4) (.var 2) (.var 1))

/-- The motive of transitivity: for `z'` and an identity proof of `y` and `z'`, the identity
type of `x` and `z'`. -/
abbrev transMotive : CTm Tower.Head 6 :=
  .lam (.var 5) (.lam (.id (.var 6) (.var 4) (.var 0)) (.id (.var 7) (.var 6) (.var 1)))

/-- The transitivity term: the identity eliminator at the motive, at the first proof, and at
the second. -/
abbrev transTerm : CTm Tower.Head 6 :=
  .app (.app (.app (.app (.app (.app (.const jName) (.var 5)) (.var 3)) transMotive)
    (.var 1)) (.var 2)) (.var 0)

theorem transMotive_inner_typed :
    CTyped objectChurch (.snoc transCtx (.var 5))
      (.lam (.id (.var 6) (.var 4) (.var 0)) (.id (.var 7) (.var 6) (.var 1)))
      (.pi (.id (.var 6) (.var 4) (.var 0)) cU0) := by
  have domain : CTyped objectChurch (.snoc transCtx (.var 5)) (.id (.var 6) (.var 4) (.var 0))
      cU0 := cidT (.var 6) (.var 4) (.var 0)
  have body : CTyped objectChurch
      (.snoc (.snoc transCtx (.var 5)) (.id (.var 6) (.var 4) (.var 0)))
      (.id (.var 7) (.var 6) (.var 1)) cU0 := cidT (.var 7) (.var 6) (.var 1)
  exact .lamIntro domain (.sort _) (cpiT (craise domain) cU0_typed) (.sort _) body

theorem transMotiveType_formed :
    CTyped objectChurch transCtx (.pi (.var 5) (.pi (.id (.var 6) (.var 4) (.var 0)) cU0))
      cU1 :=
  cpiT (craise (.var 5)) (cpiT (craise (cidT (.var 6) (.var 4) (.var 0))) cU0_typed)

theorem transMotive_typed :
    CTyped objectChurch transCtx transMotive
      (.pi (.var 5) (.pi (.id (.var 6) (.var 4) (.var 0)) cU0)) :=
  .lamIntro (.var 5) (.sort _) transMotiveType_formed (.sort _) transMotive_inner_typed

/-- The motive of transitivity at a term and an identity proof: two β-steps. -/
theorem transMotive_at {a q : CTm Tower.Head 6} (ha : CTyped objectChurch transCtx a (.var 5))
    (hq : CTyped objectChurch transCtx q (.id (.var 5) (.var 3) a)) :
    CEqual objectChurch transCtx (.app (.app transMotive a) q) (.id (.var 5) (.var 4) a) cU0 := by
  have beta₁ : CEqual objectChurch transCtx (.app transMotive a)
      (.lam (.id (.var 5) (.var 3) a) (.id (.var 6) (.var 5) (a.rename wk)))
      (.pi (.id (.var 5) (.var 3) a) cU0) :=
    .betaPi (A := .var 5) (B := .pi (.id (.var 6) (.var 4) (.var 0)) cU0)
      (body := .lam (.id (.var 6) (.var 4) (.var 0)) (.id (.var 7) (.var 6) (.var 1)))
      (a := a) transMotiveType_formed (.sort _) transMotive_inner_typed ha
  have domain : CTyped objectChurch transCtx (.id (.var 5) (.var 3) a) cU0 :=
    cidT (.var 5) (.var 3) ha
  have body : CTyped objectChurch (.snoc transCtx (.id (.var 5) (.var 3) a))
      (.id (.var 6) (.var 5) (a.rename wk)) cU0 :=
    cidT (.var 6) (.var 5) (CTyped.weaken ha)
  have beta₂ : CEqual objectChurch transCtx
      (.app (.lam (.id (.var 5) (.var 3) a) (.id (.var 6) (.var 5) (a.rename wk))) q)
      (.id (.var 5) (.var 4) (CTm.inst0 q (a.rename wk))) cU0 :=
    .betaPi (A := .id (.var 5) (.var 3) a) (B := cU0)
      (body := .id (.var 6) (.var 5) (a.rename wk)) (a := q)
      (cpiT (craise domain) cU0_typed) (.sort _) body hq
  rw [CTm.inst0_rename_wk] at beta₂
  exact .trans (.appCong (B := cU0) beta₁ (.refl hq)) beta₂

/-- **Transitivity from the identity eliminator**, over the context of its data. -/
theorem transTerm_typed :
    CTyped objectChurch transCtx transTerm (.id (.var 5) (.var 4) (.var 2)) := by
  have eliminator : CTyped objectChurch transCtx (.const jName)
      (.pi cU0 (.pi (.var 0)
        (.pi (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) cU0))
          (.pi (.app (.app (.var 0) (.var 1)) (.refl (.var 1)))
            (.pi (.var 3) (.pi (.id (.var 4) (.var 3) (.var 0))
              (.app (.app (.var 3) (.var 1)) (.var 0)))))))) := cj_typed
  have atType := CDerivable.appElim eliminator (CDerivable.var (Γ := transCtx) 5)
  have atMiddle := CDerivable.appElim atType (CDerivable.var (Γ := transCtx) 3)
  have atMotive := CDerivable.appElim atMiddle transMotive_typed
  have base : CTyped objectChurch transCtx (.var 1)
      (.app (.app transMotive (.var 3)) (.refl (.var 3))) :=
    .conv (.var 1) (.symm (transMotive_at (.var 3) (.reflIntro (.var 3)))) (.sort _)
  have atBase := CDerivable.appElim atMotive base
  have atRight := CDerivable.appElim atBase (CDerivable.var (Γ := transCtx) 2)
  have atProof := CDerivable.appElim atRight (CDerivable.var (Γ := transCtx) 0)
  exact .conv atProof (transMotive_at (.var 2) (.var 0)) (.sort _)

/-- The instance of the transitivity term at given data. -/
abbrev transOf {n : Nat} (A x y z p q : CTm Tower.Head n) : CTm Tower.Head n :=
  transTerm.subst fun i => [q, p, z, y, x, A].getD i.val A

/-- **Transitivity of identity proofs.** -/
theorem trans_typed {n : Nat} {Γ : CCtx Tower.Head n} {A x y z p q : CTm Tower.Head n}
    (hA : CTyped objectChurch Γ A cU0) (hx : CTyped objectChurch Γ x A)
    (hy : CTyped objectChurch Γ y A) (hz : CTyped objectChurch Γ z A)
    (hp : CTyped objectChurch Γ p (.id A x y)) (hq : CTyped objectChurch Γ q (.id A y z)) :
    CTyped objectChurch Γ (transOf A x y z p q) (.id A x z) :=
  transTerm_typed.substitute (σ := fun i => [q, p, z, y, x, A].getD i.val A)
    (fun j => match j with
      | ⟨0, _⟩ => hq
      | ⟨1, _⟩ => hp
      | ⟨2, _⟩ => hz
      | ⟨3, _⟩ => hy
      | ⟨4, _⟩ => hx
      | ⟨5, _⟩ => hA)

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
