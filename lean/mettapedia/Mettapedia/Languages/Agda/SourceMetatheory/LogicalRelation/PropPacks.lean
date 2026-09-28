import Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

/-!
Proposition-valued semantic clauses for the frozen finite-Set/relevant-Pi
source. The explicit-pack encoding follows the inspected Prime normalization
Definition module; no Prime presentation, cumulative universe law, or Agda
presentation is imported. Actual source evidence occurs under Nonempty.

These clauses alone assert no fundamental theorem, Pi injectivity for source
equality, general subject reduction, or decision procedure.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.StaticMetatheory
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

structure Pack (n : Nat) where
  eqTy : Ty n → Prop
  redTm : Term n → Prop
  eqTm : Term n → Term n → Prop

abbrev Relation := {n : Nat} → RawContext n → Ty n → Pack n → Prop

structure PiFamily (Γ : RawContext n) (A : Ty n) (B : TyAbs n) where
  domain : {m : Nat} → {Δ : RawContext m} → {ρ : Renaming n m} → World Γ Δ ρ → Pack m
  codomain : {m : Nat} → {Δ : RawContext m} → {ρ : Renaming n m} →
    (w : World Γ Δ ρ) → {a : Term m} → (domain w).redTm a → Pack m
  extension : {m : Nat} → {Δ : RawContext m} → {ρ : Renaming n m} →
    (w : World Γ Δ ρ) → {a b : Term m} →
    (left : (domain w).redTm a) → (domain w).redTm b → (domain w).eqTm a b →
    (codomain w left).eqTy ((B.rename ρ).instantiate b)

def neutralPack (Γ : RawContext n) (A : Ty n) : Pack n where
  eqTy B := ∃ C, Nonempty (TypeRed Γ B C) ∧ Nonempty (Neutral C.term) ∧
    Nonempty (TypeEq Γ A C)
  redTm t := ∃ nf, Nonempty (TypedRed Γ t nf A) ∧ Nonempty (Neutral nf)
  eqTm t u := ∃ nf ng, Nonempty (TypedRed Γ t nf A) ∧
    Nonempty (TypedRed Γ u ng A) ∧ Nonempty (Neutral nf) ∧ Nonempty (Neutral ng) ∧
    Nonempty (TermEq Γ nf ng A)

def PiRedTm {Γ : RawContext n} {A : Ty n} {B : TyAbs n}
    (P : PiFamily Γ A B) (t : Term n) : Prop :=
  ∃ nf, Nonempty (TypedRed Γ t nf (Ty.pi A B)) ∧ Nonempty (FunctionHead nf) ∧
    (∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (w : World Γ Δ ρ)
      {a : Term m} (argument : (P.domain w).redTm a),
      (P.codomain w argument).redTm ((nf.rename ρ).app a)) ∧
    (∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (w : World Γ Δ ρ)
      {a b : Term m} (left : (P.domain w).redTm a), (P.domain w).redTm b →
      (P.domain w).eqTm a b →
      (P.codomain w left).eqTm ((nf.rename ρ).app a) ((nf.rename ρ).app b))

def piPack (Γ : RawContext n) (A : Ty n) (B : TyAbs n) (P : PiFamily Γ A B) : Pack n where
  eqTy C := ∃ A' B', Nonempty (TypeRed Γ C (Ty.pi A' B')) ∧
    Nonempty (TypeEq Γ (Ty.pi A B) (Ty.pi A' B')) ∧
    (∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (w : World Γ Δ ρ),
      (P.domain w).eqTy (A'.rename ρ)) ∧
    (∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (w : World Γ Δ ρ)
      {a : Term m} (argument : (P.domain w).redTm a),
      (P.codomain w argument).eqTy ((B'.rename ρ).instantiate a))
  redTm := PiRedTm P
  eqTm t u := PiRedTm P t ∧ PiRedTm P u ∧
    ∃ nf ng, Nonempty (TypedRed Γ t nf (Ty.pi A B)) ∧
      Nonempty (TypedRed Γ u ng (Ty.pi A B)) ∧
      Nonempty (TermEq Γ nf ng (Ty.pi A B)) ∧
      (∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (w : World Γ Δ ρ)
        {a : Term m} (argument : (P.domain w).redTm a),
        (P.codomain w argument).eqTm ((nf.rename ρ).app a) ((ng.rename ρ).app a))

def universePack (lower : Nat → Relation) (Γ : RawContext n) (k : Nat) : Pack n where
  eqTy B := Nonempty (TypeRed Γ B (Ty.universe k))
  redTm t := ∃ nf, Nonempty (TypedRed Γ t nf (Ty.universe k)) ∧
    Nonempty (TypeHead nf) ∧ ∃ P, lower k Γ (.el k t) P
  eqTm t u := ∃ nf ng, Nonempty (TypedRed Γ t nf (Ty.universe k)) ∧
    Nonempty (TypedRed Γ u ng (Ty.universe k)) ∧
    Nonempty (TypeHead nf) ∧ Nonempty (TypeHead ng) ∧
    Nonempty (TermEq Γ nf ng (Ty.universe k)) ∧
    (∃ Q, lower k Γ (.el k u) Q) ∧ ∃ P, lower k Γ (.el k t) P ∧ P.eqTy (.el k u)

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
