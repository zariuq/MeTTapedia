import Mettapedia.Languages.Agda.SourceMetatheory.WeakHeadTransport

/-!
Typed renaming worlds for a subsequent source logical relation. Worlds retain
their context derivations and act on actual typing, equality and contraction
evidence. No reducibility, normalization or injectivity law is postulated.
Composition here does not assert equality of retained context receipts.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.Kripke
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead

structure World (Γ : RawContext n) (Δ : RawContext m) (ρ : Renaming n m) where
  sourceFormed : FormCtx Γ
  targetFormed : FormCtx Δ
  respects : ρ.Respects Γ Δ

def World.identity {Γ : RawContext n} (formed : FormCtx Γ) : World Γ Γ id :=
  ⟨formed, formed, Renaming.respects_id Γ⟩

def World.comp {Γ : RawContext n} {Δ : RawContext m} {Θ : RawContext k}
    {ρ : Renaming n m} {τ : Renaming m k} (first : World Γ Δ ρ) (second : World Δ Θ τ) :
    World Γ Θ (τ ∘ ρ) where
  sourceFormed := first.sourceFormed
  targetFormed := second.targetFormed
  respects := fun i => by
    calc
      Θ.lookup (τ (ρ i)) = (Δ.lookup (ρ i)).rename τ := second.respects (ρ i)
      _ = ((Γ.lookup i).rename ρ).rename τ := congrArg (Ty.rename τ) (first.respects i)
      _ = (Γ.lookup i).rename (τ ∘ ρ) := Ty.rename_comp _ ρ τ

def World.weaken {Γ : RawContext n} {A : Ty n} (domain : FormTy Γ A) :
    World Γ (Γ.snoc A) Fin.succ :=
  ⟨domain.context, .snoc domain.context domain, Renaming.respects_weaken Γ A⟩

def World.lift {Γ : RawContext n} {Δ : RawContext m} {ρ : Renaming n m}
    (world : World Γ Δ ρ) {A : Ty n} (domain : FormTy Γ A) :
    World (Γ.snoc A) (Δ.snoc (A.rename ρ)) (Renaming.lift ρ) :=
  ⟨.snoc world.sourceFormed domain,
    .snoc world.targetFormed (domain.rename ρ world.respects world.targetFormed),
    world.respects.lift A⟩

def World.typing {Γ : RawContext n} {Δ : RawContext m} {ρ : Renaming n m}
    (world : World Γ Δ ρ) {t : Term n} {A : Ty n} (typed : Typing Γ t A) :
    Typing Δ (t.rename ρ) (A.rename ρ) :=
  typed.rename ρ world.respects world.targetFormed

def World.typeEquality {Γ : RawContext n} {Δ : RawContext m} {ρ : Renaming n m}
    (world : World Γ Δ ρ) {A B : Ty n} (eq : TypeEq Γ A B) :
    TypeEq Δ (A.rename ρ) (B.rename ρ) :=
  eq.rename ρ world.respects world.targetFormed

def World.termEquality {Γ : RawContext n} {Δ : RawContext m} {ρ : Renaming n m}
    (world : World Γ Δ ρ) {t u : Term n} {A : Ty n} (eq : TermEq Γ t u A) :
    TermEq Δ (t.rename ρ) (u.rename ρ) (A.rename ρ) :=
  eq.rename ρ world.respects world.targetFormed

def World.reduction {Γ : RawContext n} {Δ : RawContext m} {ρ : Renaming n m}
    (world : World Γ Δ ρ) {t u : Term n} {A : Ty n} (red : TypedRed Γ t u A) :
    TypedRed Δ (t.rename ρ) (u.rename ρ) (A.rename ρ) :=
  red.rename ρ world.respects world.targetFormed

/-- The fresh variable supplies the neutral argument used to recover a
dependent codomain equation from a future Kripke Pi comparison. -/
def freshVariable {Γ : RawContext n} {A : Ty n} (domain : FormTy Γ A) :
    Typing (Γ.snoc A) (.var 0) A.weaken × Neutral (Term.var (n := n + 1) 0) :=
  ⟨.var 0 (.snoc domain.context domain), .var 0⟩

end Mettapedia.Languages.Agda.SourceMetatheory.Kripke
