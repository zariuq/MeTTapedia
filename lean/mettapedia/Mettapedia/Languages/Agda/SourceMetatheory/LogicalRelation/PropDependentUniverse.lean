import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropLift
import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropUniverses

/-!
A genuinely dependent semantic Pi: (X : Set k) -> X. Universe membership
supplies only existential relation evidence. The concrete codomain pack is
the canonical predicate union; coherence and semantic bound lifting prove
that it satisfies the required Pi clauses without extracting a pack from
Prop into Type.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

theorem universeMember_decode {bound k : Nat} (less : k < bound)
    {Γ : RawContext n} {t : Term n} (member : (universePack (below bound) Γ k).redTm t) :
    LogRel k Γ (.el k t) (canonicalPack k Γ (.el k t)) := by
  obtain ⟨_, _, _, P, related⟩ := member
  exact canonicalPack_related ⟨P, (below_iff less).mp related⟩

theorem universeEquality_decode {bound k : Nat} (less : k < bound)
    {Γ : RawContext n} {t u : Term n}
    (equal : (universePack (below bound) Γ k).eqTm t u) :
    (canonicalPack k Γ (.el k t)).eqTy (.el k u) := by
  obtain ⟨_, _, _, _, _, _, _, _, P, related, equal⟩ := equal
  have atLevel := (below_iff less).mp related
  rw [atLevel.canonicalPack_eq]
  exact equal

def elementBody (n k : Nat) : TyAbs n := .bind (.el k (.var 0))

@[simp] theorem elementBody_instantiate (k : Nat) (ρ : Renaming n m) (a : Term m) :
    ((elementBody n k).rename ρ).instantiate a = .el k a := rfl

def universeFamily (Γ : RawContext n) (k : Nat) :
    PiFamily Γ (Ty.universe k) (elementBody n k) where
  domain {_m} {Δ} {_ρ} _world := universePack (below (k + 1)) Δ k
  codomain {_m} {Δ} {_ρ} _world {a} _argument := canonicalPack k Δ (.el k a)
  extension {_m} {_Δ} {_ρ} _world {_a} {_b} _left _right equal :=
    universeEquality_decode (Nat.lt_succ_self k) equal

def elementBody_formed {Γ : RawContext n} (formed : FormCtx Γ) (k : Nat) :
    FormTy (Γ.snoc (Ty.universe k)) (elementBody n k).open :=
  .ofTyping (by simpa only [RawContext.lookup_zero, Ty.weaken, Ty.universe_rename] using
    (Typing.var 0 (FormCtx.snoc formed (FormTy.universe formed k))))

theorem universePiRelated {Γ : RawContext n} (formed : FormCtx Γ) (k : Nat) :
    LogRel (k + 1) Γ (Ty.pi (Ty.universe k) (elementBody n k))
      (piPack Γ (Ty.universe k) (elementBody n k) (universeFamily Γ k)) := by
  have domain : FormTy Γ (Ty.universe k) := .ofTyping (.sort k formed)
  have codomain := elementBody_formed formed k
  refine LR.pi ⟨.refl (.pi domain codomain)⟩ ⟨domain⟩ ⟨codomain⟩
    (universeFamily Γ k) ?_ ?_
  · intro m Δ ρ world
    simpa only [Ty.universe_rename, universeFamily, LogRel] using
      universeReducible (k + 1) k (Nat.lt_succ_self k) world.targetFormed
  · intro m Δ ρ world a argument
    exact LogRel.raise (Nat.le_succ k) (universeMember_decode (Nat.lt_succ_self k) argument)

/-- The codomain tracks the supplied type code, not a fixed domain code. -/
theorem universeFamily_codomain {Γ : RawContext n} (k : Nat)
    {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ) {a : Term m}
    (argument : ((universeFamily Γ k).domain world).redTm a) :
    (universeFamily Γ k).codomain world argument = canonicalPack k Δ (.el k a) := rfl

/-- Both a semantic type and its actual source formation can be recovered
from a universe argument in every formed world. -/
def universeArgument_formation {Γ : RawContext n} (k : Nat)
    {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ) {a : Term m}
    (argument : ((universeFamily Γ k).domain world).redTm a) : FormTy Δ (.el k a) :=
  Mettapedia.Languages.Agda.SourceEvidence.Codec.recoverFormation
    (universeMember_decode (Nat.lt_succ_self k) argument).escape.formation

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
