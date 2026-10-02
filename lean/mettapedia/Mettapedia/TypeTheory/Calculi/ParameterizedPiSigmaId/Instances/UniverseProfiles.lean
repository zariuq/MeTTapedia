import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
import Mettapedia.TypeTheory.UniverseLevel.Algebra

/-!
# Two-sort and cumulative universe profiles

These distinct rule instances share the parameterized syntax. The two-sort
profile represents the historical MeTTaPure experiment, not a selected Prime
kernel. The embedding sends its ground head to an opaque ground head, not to
the bottom universe of the cumulative profile.
-/

open Mettapedia.TypeTheory.UniverseLevel

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

/-! ## The sealed legacy presentation -/

namespace Legacy

/-- The old heads, named by their actual roles rather than `u0`/`u1`. -/
inductive Head where
  | ground
  | marker
  deriving DecidableEq, Repr

abbrev Tm (n : Nat) := Presentation.Tm Head n
abbrev Ctx (n : Nat) := Presentation.Ctx Head n

inductive HeadTyping : Head → Head → Prop where
  | groundMarker : HeadTyping .ground .marker

inductive IsUniverse : Head → Prop where
  | marker : IsUniverse .marker

inductive Join : Head → Head → Head → Prop where
  | marker : Join .marker .marker .marker

/-- The sealed fragment has no cumulative lifting rule. -/
def Cumulative (_ _ : Head) : Prop := False

/-- Legacy head equality is ordinary constructor equality. -/
def HeadEq (left right : Head) : Prop := left = right

def rules : Rules Head where
  headTyping := HeadTyping
  isUniverse := IsUniverse
  join := Join
  cumulative := Cumulative
  headEq := HeadEq

abbrev HasType {n : Nat} := @Presentation.HasType Head rules n

/-- Exact re-presentation of the existing sealed grammar. -/
def ofTwoSort :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax.ScopedTerm n → Tm n
  | .var i => .var i
  | .const c => .const c
  | .u0 => .head .ground
  | .u1 => .head .marker
  | .pi A B => .pi (ofTwoSort A) (ofTwoSort B)
  | .sigma A B => .sigma (ofTwoSort A) (ofTwoSort B)
  | .id A a b => .id (ofTwoSort A) (ofTwoSort a) (ofTwoSort b)
  | .lam body => .lam (ofTwoSort body)
  | .app g a => .app (ofTwoSort g) (ofTwoSort a)
  | .pair a b => .pair (ofTwoSort a) (ofTwoSort b)
  | .fst p => .fst (ofTwoSort p)
  | .snd p => .snd (ofTwoSort p)
  | .refl a => .refl (ofTwoSort a)

/-- Inverse translation back to the existing sealed grammar. -/
def toTwoSort : Tm n →
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax.ScopedTerm n
  | .var i => .var i
  | .const c => .const c
  | .head .ground => .u0
  | .head .marker => .u1
  | .pi A B => .pi (toTwoSort A) (toTwoSort B)
  | .sigma A B => .sigma (toTwoSort A) (toTwoSort B)
  | .id A a b => .id (toTwoSort A) (toTwoSort a) (toTwoSort b)
  | .lam body => .lam (toTwoSort body)
  | .app g a => .app (toTwoSort g) (toTwoSort a)
  | .pair a b => .pair (toTwoSort a) (toTwoSort b)
  | .fst p => .fst (toTwoSort p)
  | .snd p => .snd (toTwoSort p)
  | .refl a => .refl (toTwoSort a)

@[simp] theorem toTwoSort_ofTwoSort
    (t : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax.ScopedTerm n) :
    toTwoSort (ofTwoSort t) = t := by
  induction t with
  | var i => rfl
  | const c => rfl
  | u0 => rfl
  | u1 => rfl
  | pi A B ihA ihB => simp only [ofTwoSort, toTwoSort, ihA, ihB]
  | sigma A B ihA ihB => simp only [ofTwoSort, toTwoSort, ihA, ihB]
  | id A a b ihA iha ihb => simp only [ofTwoSort, toTwoSort, ihA, iha, ihb]
  | lam body ih => simp only [ofTwoSort, toTwoSort, ih]
  | app g a ihg iha => simp only [ofTwoSort, toTwoSort, ihg, iha]
  | pair a b iha ihb => simp only [ofTwoSort, toTwoSort, iha, ihb]
  | fst p ih => simp only [ofTwoSort, toTwoSort, ih]
  | snd p ih => simp only [ofTwoSort, toTwoSort, ih]
  | refl a ih => simp only [ofTwoSort, toTwoSort, ih]

@[simp] theorem ofTwoSort_toTwoSort (t : Tm n) : ofTwoSort (toTwoSort t) = t := by
  induction t with
  | var i => rfl
  | const c => rfl
  | head h => cases h <;> rfl
  | pi A B ihA ihB => simp only [toTwoSort, ofTwoSort, ihA, ihB]
  | sigma A B ihA ihB => simp only [toTwoSort, ofTwoSort, ihA, ihB]
  | id A a b ihA iha ihb => simp only [toTwoSort, ofTwoSort, ihA, iha, ihb]
  | lam body ih => simp only [toTwoSort, ofTwoSort, ih]
  | app g a ihg iha => simp only [toTwoSort, ofTwoSort, ihg, iha]
  | pair a b iha ihb => simp only [toTwoSort, ofTwoSort, iha, ihb]
  | fst p ih => simp only [toTwoSort, ofTwoSort, ih]
  | snd p ih => simp only [toTwoSort, ofTwoSort, ih]
  | refl a ih => simp only [toTwoSort, ofTwoSort, ih]

end Legacy

/-! ## The cumulative tower presentation -/

/-! ### The tower over a level order

An opaque legacy ground head plus one predicative universe for every level expression
over the level order `L`. -/

namespace LevelTower

open Mettapedia.TypeTheory.UniverseLevel

/-- The heads of the tower: an opaque legacy ground head plus explicit predicative
universe levels. -/
inductive Head (L : Type) where
  | legacyGround
  | sort : LevelExpr L → Head L
  deriving DecidableEq, Repr

abbrev Tm (L : Type) (n : Nat) := Presentation.Tm (Head L) n
abbrev Ctx (L : Type) (n : Nat) := Presentation.Ctx (Head L) n

variable {L : Type}

/-- The least level, as a level expression. -/
def zero [LevelOrder L] : LevelExpr L := .const LevelOrder.bot

/-- The least level evaluates to the least level. -/
@[simp] theorem eval_zero [LevelOrder L] (v : Nat → L) :
    LevelExpr.eval v (zero : LevelExpr L) = LevelOrder.bot := rfl

inductive HeadTyping [LevelOrder L] : Head L → Head L → Prop where
  | legacyGround : HeadTyping .legacyGround (.sort zero)
  | sort (level : LevelExpr L) : HeadTyping (.sort level) (.sort (.succ level))

inductive IsUniverse : Head L → Prop where
  | sort (level : LevelExpr L) : IsUniverse (.sort level)

/-- Pi, Sigma, and identity formation live in the maximum input
universe.  Semantic level conversion may subsequently canonicalize it. -/
inductive Join : Head L → Head L → Head L → Prop where
  | sorts (left right : LevelExpr L) :
      Join (.sort left) (.sort right) (.sort (.max left right))

/-- Cumulativity is semantic order of explicit levels. -/
def Cumulative [LevelOrder L] : Head L → Head L → Prop
  | .sort left, .sort right =>
      ∀ v, LevelExpr.eval v left ≤ LevelExpr.eval v right
  | _, _ => False

/-- Universe heads are convertible exactly when their explicit levels
denote the same value under every valuation.  The opaque ground head only
converts to itself. -/
def HeadEq [LevelOrder L] : Head L → Head L → Prop
  | .legacyGround, .legacyGround => True
  | .sort left, .sort right =>
      ∀ v, LevelExpr.eval v left = LevelExpr.eval v right
  | _, _ => False

instance instDecidableCumulative [LevelOrder L] (left right : Head L) :
    Decidable (Cumulative left right) := by
  unfold Cumulative
  split <;> infer_instance

instance instDecidableHeadEq [LevelOrder L] (left right : Head L) :
    Decidable (HeadEq left right) := by
  unfold HeadEq
  split <;> infer_instance

/-- The rules of the tower over the level order `L`. -/
def rules (L : Type) [LevelOrder L] : Rules (Head L) where
  headTyping := HeadTyping
  isUniverse := IsUniverse
  join := Join
  cumulative := Cumulative
  headEq := HeadEq

abbrev HasType [LevelOrder L] {n : Nat} := @Presentation.HasType (Head L) (rules L) n

end LevelTower

/-! ### The tower over the natural numbers

The finite levels: the instance of the tower at the natural numbers. -/

namespace Tower

open Mettapedia.TypeTheory.UniverseLevel

abbrev Head := LevelTower.Head Nat
abbrev Tm (n : Nat) := LevelTower.Tm Nat n
abbrev Ctx (n : Nat) := LevelTower.Ctx Nat n
abbrev zero : LevelExpr Nat := LevelTower.zero
abbrev HeadTyping : Head → Head → Prop := LevelTower.HeadTyping
abbrev IsUniverse : Head → Prop := LevelTower.IsUniverse
abbrev Join : Head → Head → Head → Prop := LevelTower.Join
abbrev Cumulative : Head → Head → Prop := LevelTower.Cumulative
abbrev HeadEq : Head → Head → Prop := LevelTower.HeadEq
abbrev rules : Rules Head := LevelTower.rules Nat
abbrev HasType {n : Nat} := @Presentation.HasType Head rules n

end Tower

/-- The tower universe term at an explicit level.  This constructor belongs
to the shared cumulative presentation rather than to any particular schema
elaboration. -/
def sortTm (level : LevelExpr Nat) : Tower.Tm n := .head (.sort level)

/-! ## The migration map and executable boundary witnesses -/

namespace Legacy.Head

/-- The only sanctioned head migration.  In particular, `ground` does not
map to `Tower.sort Tower.zero`. -/
def embed : Legacy.Head → Tower.Head
  | .ground => .legacyGround
  | .marker => .sort Tower.zero

theorem embed_injective : Function.Injective embed := by
  intro left right h
  cases left <;> cases right <;> simp [embed] at h ⊢

end Legacy.Head

namespace Tower.Head

/-- Forget all explicit tower levels while preserving the distinction
between the legacy ground head and universe heads.  This is a syntactic
retraction of `Legacy.Head.embed`, not a typing translation for arbitrary
tower terms. -/
def forget : Tower.Head → Legacy.Head
  | .legacyGround => .ground
  | .sort _ => .marker

@[simp] theorem forget_embed (head : Legacy.Head) :
    forget head.embed = head := by
  cases head <;> rfl

end Tower.Head

namespace Legacy

/-- Structural embedding of sealed terms into the cumulative presentation. -/
def embed (t : Tm n) : Tower.Tm n := t.mapHead Head.embed

/-- Context embedding uses the same structural head map. -/
def embedCtx (Γ : Ctx n) : Tower.Ctx n := Γ.mapHead Head.embed

/-- Erase explicit levels from tower syntax.  This is used only as a
syntactic retraction and as a conversion invariant; arbitrary erased tower
typing derivations need not be legacy derivations. -/
def forget (t : Tower.Tm n) : Tm n := t.mapHead Tower.Head.forget

/-- Level erasure on contexts. -/
def forgetCtx (Γ : Tower.Ctx n) : Ctx n := Γ.mapHead Tower.Head.forget

@[simp] theorem forget_embed (t : Tm n) : forget (embed t) = t := by
  rw [forget, embed, Tm.mapHead_comp]
  simp [Function.comp_def]

theorem embed_injective : Function.Injective (@embed n) := by
  intro left right h
  have := congrArg forget h
  simpa using this

@[simp] theorem forgetCtx_embedCtx (Γ : Ctx n) :
    forgetCtx (embedCtx Γ) = Γ := by
  induction Γ with
  | nil => rfl
  | snoc Γ A ih =>
      simp only [forgetCtx, embedCtx, Ctx.mapHead]
      have hA : Tm.mapHead Tower.Head.forget
          (Tm.mapHead Head.embed A) = A := by
        rw [Tm.mapHead_comp]
        simp [Function.comp_def]
      exact congrArg₂ Ctx.snoc ih hA

end Legacy

/-- Positive legacy witness: the distinguished ground type is typed by the
sealed marker. -/
example : Legacy.HasType (.nil : Legacy.Ctx 0)
    (.head .ground) (.head .marker) :=
  .headType .groundMarker

/-- Negative legacy witness: the marker itself has no head-typing rule. -/
example : ¬ Legacy.HeadTyping .marker candidate := by
  intro h
  cases h

/-- Positive tower witness: every explicit sort inhabits its successor. -/
example (level :
    Mettapedia.TypeTheory.UniverseLevel.LevelExpr Nat) :
    Tower.HasType (.nil : Tower.Ctx 0)
      (.head (.sort level)) (.head (.sort (.succ level))) :=
  .headType (.sort level)

/-- Positive cumulative witness. -/
example : Tower.Cumulative (.sort (.const 0)) (.sort (.const 1)) := by
  intro v
  simp [Mettapedia.TypeTheory.UniverseLevel.LevelExpr.eval]

/-- Negative cumulative witness: successor levels cannot be lowered. -/
example : ¬ Tower.Cumulative (.sort (.succ (.param 0))) (.sort (.param 0)) := by
  decide

/-- The migration anti-confusion invariant is executable. -/
example : Legacy.Head.embed .ground ≠ .sort Tower.zero := by
  decide

/-- The old universe axiom embeds as ground-formation, not as the tower's
universe-successor axiom. -/
example : Tower.HasType (.nil : Tower.Ctx 0)
    (Legacy.embed (.head .ground : Legacy.Tm 0))
    (Legacy.embed (.head .marker : Legacy.Tm 0)) :=
  .headType .legacyGround

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
