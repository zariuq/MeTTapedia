import Mettapedia.AutoBooks.Codex.Henkin1950.AxiomSchemes
import Mettapedia.Logic.HOL.DerivationExtensionality

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Selected derived results quoted on p. 85 of Henkin (1950).

This file focuses on the fragment whose statements are clear in the scan and
whose proofs already live in the trusted extensional HOL core currently reused
by the Codex development.
-/

/-- Closed theorems in the extensional closed-HOL calculus over Henkin's signature. -/
abbrev ExtTheorem (φ : Sentence) : Prop := ExtDerivation.Theorem Primitive φ

/-- Open theorems in the extensional HOL calculus over Henkin's signature. -/
abbrev ExtTheoremInContext {Γ : Ctx Atom} (φ : Formula Γ) : Prop :=
  ExtDerivation Primitive [] φ

/-- Promote a base-theorem proof to the extensional overlay. -/
theorem extensional_of_base {φ : Sentence} (h : Theorem φ) : ExtTheorem φ :=
  ExtDerivation.ofBase h

/-- Pointwise equality formula used as an extensional helper. -/
def pointwiseEq {α β : HTy} (f g : ClosedTerm (α ⇒ β)) : Formula [α] :=
  eq (.app (weaken f) (var0 α)) (.app (weaken g) (var0 α))

/-- Quoted result 12: `A -> (~A -> B)`. -/
theorem derived12 (A B : Sentence) :
    ExtTheorem (imp A (imp (not A) B)) := by
  refine .impI ?_
  refine .impI ?_
  have hNotA : ExtDerivation Primitive [not A, A] (not A) :=
    .hyp (show not A ∈ [not A, A] from by simp)
  have hA : ExtDerivation Primitive [not A, A] A :=
    .hyp (show A ∈ [not A, A] from by simp)
  exact .botE (.notE hNotA hA)

/-- Quoted result 14: `A = A`. -/
theorem derived14 {α : HTy} (t : ClosedTerm α) :
    ExtTheorem (eq t t) :=
  .eqRefl t

/-- Quoted result 15: `A = B -> B = A`. -/
theorem derived15 {α : HTy} (t u : ClosedTerm α) :
    ExtTheorem (imp (eq t u) (eq u t)) := by
  refine .impI ?_
  have hEq : ExtDerivation Primitive [eq t u] (eq t u) :=
    .hyp (show eq t u ∈ [eq t u] from by simp)
  exact .eqSymm hEq

/-- Quoted result 16: `A = B -> (B = C -> A = C)`. -/
theorem derived16 {α : HTy} (t u v : ClosedTerm α) :
    ExtTheorem (imp (eq t u) (imp (eq u v) (eq t v))) := by
  refine .impI ?_
  refine .impI ?_
  have htu : ExtDerivation Primitive [eq u v, eq t u] (eq t u) :=
    .hyp (show eq t u ∈ [eq u v, eq t u] from by simp)
  have huv : ExtDerivation Primitive [eq u v, eq t u] (eq u v) :=
    .hyp (show eq u v ∈ [eq u v, eq t u] from by simp)
  exact .eqTrans htu huv

/-- Quoted result 17: `A -> ((A = B) -> B)`. -/
theorem derived17 (A B : Sentence) :
    ExtTheorem (imp A (imp (eq A B) B)) := by
  refine .impI ?_
  refine .impI ?_
  have hEq : ExtDerivation Primitive [eq A B, A] (eq A B) :=
    .hyp (show eq A B ∈ [eq A B, A] from by simp)
  have hA : ExtDerivation Primitive [eq A B, A] A :=
    .hyp (show A ∈ [eq A B, A] from by simp)
  exact ExtDerivation.eqProp_mp_left hEq hA

/-- Quoted result 18: `~A -> ((A = B) -> ~B)`. -/
theorem derived18 (A B : Sentence) :
    ExtTheorem (imp (not A) (imp (eq A B) (not B))) := by
  refine .impI ?_
  refine .impI ?_
  refine .notI ?_
  have hEq : ExtDerivation Primitive [B, eq A B, not A] (eq A B) :=
    .hyp (by simp [eq, not])
  have hB : ExtDerivation Primitive [B, eq A B, not A] B :=
    .hyp (by simp)
  have hA : ExtDerivation Primitive [B, eq A B, not A] A :=
    ExtDerivation.eqProp_mp_right hEq hB
  exact .notE (.hyp (by simp [not])) hA

/-- Quoted result 19: `A -> (B -> A = B)`. -/
theorem derived19 (A B : Sentence) :
    ExtTheorem (imp A (imp B (eq A B))) := by
  refine .impI ?_
  refine .impI ?_
  refine ExtDerivation.eqPropI ?_ ?_
  · refine .impI ?_
    exact .hyp (show B ∈ [A, B, A] from by simp)
  · refine .impI ?_
    exact .hyp (show A ∈ [B, B, A] from by simp)

/-- Quoted result 20: `~A -> (~B -> A = B)`. -/
theorem derived20 (A B : Sentence) :
    ExtTheorem (imp (not A) (imp (not B) (eq A B))) := by
  refine .impI ?_
  refine .impI ?_
  refine ExtDerivation.eqPropI ?_ ?_
  · refine .impI ?_
    have hNotA : ExtDerivation Primitive [A, not B, not A] (not A) :=
      .hyp (show not A ∈ [A, not B, not A] from by simp)
    have hA : ExtDerivation Primitive [A, not B, not A] A :=
      .hyp (show A ∈ [A, not B, not A] from by simp)
    exact .botE (.notE hNotA hA)
  · refine .impI ?_
    have hNotB : ExtDerivation Primitive [B, not B, not A] (not B) :=
      .hyp (show not B ∈ [B, not B, not A] from by simp)
    have hB : ExtDerivation Primitive [B, not B, not A] B :=
      .hyp (show B ∈ [B, not B, not A] from by simp)
    exact .botE (.notE hNotB hB)

/-- Quoted result 21: equality is congruent under application. -/
theorem derived21 {α β : HTy} (f g : ClosedTerm (α ⇒ β)) (t u : ClosedTerm α) :
    ExtTheorem (imp (eq f g) (imp (eq t u) (eq (.app f t) (.app g u)))) := by
  refine .impI ?_
  refine .impI ?_
  exact ExtDerivation.eqAppCongr
    (.hyp (show eq f g ∈ [eq t u, eq f g] from by simp))
    (.hyp (show eq t u ∈ [eq t u, eq f g] from by simp))

/-- Helper: function equality implies pointwise equality. -/
theorem pointwiseEq_of_eq {α β : HTy} (f g : ClosedTerm (α ⇒ β)) :
    ExtTheorem (imp (eq f g) (forall_ (pointwiseEq f g))) := by
  refine .impI ?_
  refine .allI ?_
  simp only [pointwiseEq, eq, var0, weakenHyps]
  exact
    (ExtDerivation.eqApp (var0 α)
      (.hyp (show weaken (eq f g) ∈
          weakenHyps (Base := Atom) (Const := Primitive) (σ := α) [eq f g] from by
        simp [weakenHyps])))

/-- Helper: pointwise equality implies function equality. -/
theorem eq_of_pointwiseEq {α β : HTy} (f g : ClosedTerm (α ⇒ β)) :
    ExtTheorem (imp (forall_ (pointwiseEq f g)) (eq f g)) := by
  refine .impI ?_
  have hAll :
      ExtDerivation Primitive [forall_ (pointwiseEq f g)]
        (.all (.eq (.app (weaken f) (.var .vz)) (.app (weaken g) (.var .vz)))) := by
    simpa [forall_, pointwiseEq, eq, var0] using
      (.hyp (show forall_ (pointwiseEq f g) ∈ [forall_ (pointwiseEq f g)] from by simp))
  exact .funExt hAll

/-- Quoted result 23: `A -> ~~A`. -/
theorem derived23 (A : Sentence) :
    ExtTheorem (imp A (not (not A))) := by
  refine .impI ?_
  refine .notI ?_
  have hNotA : ExtDerivation Primitive [not A, A] (not A) :=
    .hyp (show not A ∈ [not A, A] from by simp)
  have hA : ExtDerivation Primitive [not A, A] A :=
    .hyp (show A ∈ [not A, A] from by simp)
  exact .notE hNotA hA

/-- Quoted result 24: `C -> (C v A)`. -/
theorem derived24 (C A : Sentence) :
    ExtTheorem (imp C (or C A)) :=
  extensional_of_base (axiom2_theorem C A)

/-- Quoted result 25: `A -> (C v A)`. -/
theorem derived25 (C A : Sentence) :
    ExtTheorem (imp A (or C A)) := by
  refine .impI ?_
  exact .orIR (.hyp (show A ∈ [A] from by simp))

/-- Quoted result 26: `~C -> (~A -> ~(C v A))`. -/
theorem derived26 (C A : Sentence) :
    ExtTheorem (imp (not C) (imp (not A) (not (or C A)))) := by
  refine .impI ?_
  refine .impI ?_
  refine .notI ?_
  have hOr : ExtDerivation Primitive [or C A, not A, not C] (or C A) :=
    .hyp (show or C A ∈ [or C A, not A, not C] from by simp)
  refine .orE hOr ?_ ?_
  · have hNotC : ExtDerivation Primitive [C, or C A, not A, not C] (not C) :=
      .hyp (show not C ∈ [C, or C A, not A, not C] from by simp)
    have hC : ExtDerivation Primitive [C, or C A, not A, not C] C :=
      .hyp (show C ∈ [C, or C A, not A, not C] from by simp)
    exact .notE hNotC hC
  · have hNotA : ExtDerivation Primitive [A, or C A, not A, not C] (not A) :=
      .hyp (show not A ∈ [A, or C A, not A, not C] from by simp)
    have hA : ExtDerivation Primitive [A, or C A, not A, not C] A :=
      .hyp (show A ∈ [A, or C A, not A, not C] from by simp)
    exact .notE hNotA hA

/-- Quoted result 27: `(∀x) A x -> A t`. -/
theorem derived27 {α : HTy} (φ : Formula [α]) (t : ClosedTerm α) :
    ExtTheorem (imp (forall_ φ) (instantiate t φ)) := by
  refine .impI ?_
  exact .allE t (.hyp (by simp [forall_]))

/-- Instantiating the weakened body of a universal formula at the current variable
    recovers the original open formula. -/
theorem instantiate_liftWeaken_var0 {Γ : Ctx Atom} {α : HTy}
    (φ : Formula (α :: Γ)) :
    instantiate (.var (.vz : Var (α :: Γ) α))
      (rename
        (Rename.lift (Base := Atom) (σ := α)
          (Rename.weaken (Base := Atom) (Γ := Γ) (σ := α)))
        φ) = φ := by
  unfold instantiate
  calc
    subst
        (Subst.single (Base := Atom) (Const := Primitive)
          (.var (.vz : Var (α :: Γ) α)))
        (rename
          (Rename.lift (Base := Atom) (σ := α)
            (Rename.weaken (Base := Atom) (Γ := Γ) (σ := α)))
          φ)
      =
        subst
          (fun {τ} v =>
            (Subst.single (Base := Atom) (Const := Primitive)
              (.var (.vz : Var (α :: Γ) α)))
              ((Rename.lift (Base := Atom) (σ := α)
                (Rename.weaken (Base := Atom) (Γ := Γ) (σ := α))) v))
          φ := by
            exact subst_rename
              (Base := Atom)
              (Const := Primitive)
              (Subst.single (.var (.vz : Var (α :: Γ) α)))
              (Rename.lift
                (Base := Atom)
                (σ := α)
                (Rename.weaken (Base := Atom) (Γ := Γ) (σ := α)))
              φ
    _ =
        subst (Subst.id (Base := Atom) (Const := Primitive) (Γ := α :: Γ)) φ := by
          apply subst_ext
          intro τ v
          cases v with
          | vz => rfl
          | vs v => rfl
    _ = φ := subst_id (Base := Atom) (Const := Primitive) φ

/-- Quoted result 31: `(∀x) A -> A` as an open instantiation schema. -/
theorem derived31 {Γ : Ctx Atom} {α : HTy} (φ : Formula (α :: Γ)) :
    ExtTheoremInContext
      (imp (weaken (Base := Atom) (Const := Primitive) (σ := α) (.all φ)) φ) := by
  refine .impI ?_
  simpa [instantiate_liftWeaken_var0] using
    (ExtDerivation.allE (.var (.vz : Var (α :: Γ) α))
      (.hyp (show
        weaken (Base := Atom) (Const := Primitive) (σ := α) (.all φ) ∈
          [weaken (Base := Atom) (Const := Primitive) (σ := α) (.all φ)] from by
        simp)))

end Mettapedia.AutoBooks.Codex.Henkin1950
