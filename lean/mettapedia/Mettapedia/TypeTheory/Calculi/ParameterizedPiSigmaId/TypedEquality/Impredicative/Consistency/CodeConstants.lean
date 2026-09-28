import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Root
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Package

/-!
# The code constants in the consistency model

A package of proposition codes is read by the model when its type of codes,
decoder and implication are the model's, and each of its quantifier and
equation instances ranges over a carrier the model interprets. Its decoding
steps are then decodings of the model's codes, and each code constant is a
valid term of its declared type:

* the type of codes is a type of the lowest universe;
* the decoder sends codes with one truth value to types with one partial
  equivalence;
* implication, the quantifiers and the equation codes send arguments with
  common meanings to codes with a common truth value.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization
open TelescopeAbstraction (subst_empty)

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {M : Model Head L}

/-- A package of proposition codes read by the model. -/
structure CodesRead (M : Model Head L) (K : Codes Head) : Prop where
  proofs : M.rules.isUniverse K.proofs
  prop : K.prop = M.prop
  holds : K.holds = M.holds
  imp : K.imp = M.imp
  all : ∀ {a : DeclName} {T : Tm Head 0}, K.quantifiers a = some T →
    ∃ (k : Kind) (A : Carrier k), M.allCarrier a = some ⟨k, A⟩ ∧ A.Interpretable M ∧
      T = A.term M
  eq : ∀ {e : DeclName} {T : Tm Head 0}, K.equationCarrier e = some T →
    ∃ (k : Kind) (A : Carrier k), M.eqCarrier e = some ⟨k, A⟩ ∧ A.Interpretable M ∧
      T = A.term M

/-- The decoders of a package read by the model are the model's codes. -/
theorem CodesRead.decodes {K : Codes Head} (read : CodesRead M K) : Decodes M K.decoders where
  holds := read.holds
  imp := read.imp
  all := read.all
  eq := read.eq

/-- A closed term is a valid term of a closed type when the type has a
denotation at every world and every such denotation relates the term to
itself. -/
theorem ValidTm.closed {c T : Tm Head 0}
    (den : ∀ {m : Nat} (ξ : World M.reading m), ∃ R, Den M ξ (liftClosed T) R)
    (rel : ∀ {m : Nat} (ξ : World M.reading m) {R : Rel Head m}, Den M ξ (liftClosed T) R →
      R (liftClosed c) (liftClosed c)) : ValidTm M .nil c T := by
  refine ⟨fun {_ ξ σ σ'} _ => ?_, fun {_ ξ σ σ'} _ {R} d => ?_⟩
  · rw [subst_empty, subst_empty]
    obtain ⟨R, d⟩ := den ξ
    exact ⟨R, d, d⟩
  · rw [subst_empty] at d
    rw [subst_empty, subst_empty]
    exact rel ξ d

section Laws

variable (laws : M.Laws) {K : Codes Head} (read : CodesRead M K)
include laws read

omit laws in
/-- The universe of proofs, interpreted one level above its own. -/
theorem interp_proofs {n : Nat} (ξ : World M.reading n) :
    InterpAt M (LevelOrder.succ (M.levels.level K.proofs)) ξ (liftClosed (.head K.proofs : Tm Head 0))
      (universeRel (levelsBelow M (LevelOrder.succ (M.levels.level K.proofs)) (M.levels.level K.proofs)) ξ) :=
  Interp.sort read.proofs (LevelOrder.lt_succ _) .refl

/-- The type of codes is a valid type of the universe of proofs. -/
theorem valid_prop : ValidTm M .nil (.const K.prop) (.head K.proofs) := by
  refine ValidTm.closed (fun ξ => ⟨_, Den.sort read.proofs ξ⟩) (fun {_} ξ {R} d => ?_)
  rw [Den.sort_inv laws read.proofs d]
  intro _ ξ' _ _
  rw [read.prop]
  exact ⟨_, Interp.prop .refl, Interp.prop .refl⟩

/-- The decoder is a valid term of `prop → U`, for the universe of proofs `U`. -/
theorem valid_holds : ValidTm M .nil (.const K.holds) K.holdsType := by
  have interp : ∀ {m : Nat} (ξ : World M.reading m), ∃ R,
      InterpAt M (LevelOrder.succ (M.levels.level K.proofs)) ξ (liftClosed K.holdsType) R := by
    intro _ ξ
    rw [show K.holdsType = .pi (.const M.prop) (Presentation.rename wk (.head K.proofs)) by
      rw [← read.prop]; rfl]
    exact ⟨_, interp_arrow (Carrier.interp_prop _) (interp_proofs read) ξ⟩
  refine ValidTm.closed (fun ξ => ?_) (fun {_} ξ {R} d => ?_)
  · obtain ⟨R, h⟩ := interp ξ
    exact ⟨R, _, h⟩
  · obtain ⟨_, d⟩ := d
    rw [show K.holdsType = .pi (.const M.prop) (.head K.proofs) by
      rw [← read.prop]; rfl] at d
    rw [show (liftClosed (.const K.holds) : Tm Head _) = .const M.holds by
      rw [read.holds]; rfl]
    exact holds_sem laws d

/-- Implication is a valid term of `prop → prop → prop`. -/
theorem valid_imp : ValidTm M .nil (.const K.imp) K.impType := by
  have form : K.impType = .pi (.const M.prop) (.pi (.const M.prop) (.const M.prop)) := by
    rw [← read.prop]; rfl
  refine ValidTm.closed (fun ξ => ?_) (fun {_} ξ {R} d => ?_)
  · rw [form]
    exact ⟨_, LevelOrder.bot, interp_arrow (Carrier.interp_prop LevelOrder.bot)
      (fun ξ' => interp_arrow (Carrier.interp_prop LevelOrder.bot) (Carrier.interp_prop LevelOrder.bot) ξ') ξ⟩
  · obtain ⟨_, d⟩ := d
    rw [form] at d
    rw [show (liftClosed (.const K.imp) : Tm Head _) = .const M.imp by
      rw [read.imp]; rfl]
    exact imp_sem laws d

/-- A quantifier instance is a valid term of `(A → prop) → prop`. -/
theorem valid_all {a : DeclName} {T : Tm Head 0} (carrier : K.quantifiers a = some T) :
    ValidTm M .nil (.const a) (K.allType T) := by
  obtain ⟨_, A, carrierM, hA, rfl⟩ := read.all carrier
  have form : K.allType (A.term M) = .pi (.pi (A.term M) (.const M.prop)) (.const M.prop) := by
    rw [← read.prop]; rfl
  refine ValidTm.closed (fun ξ => ?_) (fun {_} ξ {R} d => ?_)
  · rw [form]
    exact ⟨_, LevelOrder.bot, interp_arrow
      (fun ξ' => interp_arrow (Carrier.interp_rel laws LevelOrder.bot hA) (Carrier.interp_prop LevelOrder.bot) ξ')
      (Carrier.interp_prop LevelOrder.bot) ξ⟩
  · obtain ⟨_, d⟩ := d
    rw [form] at d
    exact all_sem laws carrierM hA d

/-- An equation instance is a valid term of `A → A → prop`. -/
theorem valid_eq {e : DeclName} {T : Tm Head 0} (carrier : K.equationCarrier e = some T) :
    ValidTm M .nil (.const e) (K.eqType T) := by
  obtain ⟨_, A, carrierM, hA, rfl⟩ := read.eq carrier
  have form : K.eqType (A.term M) =
      .pi (A.term M) (.pi (Presentation.rename wk (A.term M)) (.const M.prop)) := by
    rw [← read.prop]; rfl
  refine ValidTm.closed (fun ξ => ?_) (fun {_} ξ {R} d => ?_)
  · rw [form]
    exact ⟨_, LevelOrder.bot, interp_arrow (Carrier.interp_rel laws LevelOrder.bot hA)
      (fun ξ' => interp_arrow (Carrier.interp_rel laws LevelOrder.bot hA) (Carrier.interp_prop LevelOrder.bot) ξ') ξ⟩
  · obtain ⟨_, d⟩ := d
    rw [form] at d
    exact eq_sem laws carrierM hA d

/-- Every code constant is a valid term of its declared type. -/
theorem valid_code {c : DeclName} {T : Tm Head 0} (declared : K.codeType c = some T) :
    ValidTm M .nil (.const c) T := by
  unfold Codes.codeType at declared
  by_cases hp : c = K.prop
  · rw [if_pos hp] at declared
    cases declared
    rw [hp]
    exact valid_prop laws read
  rw [if_neg hp] at declared
  by_cases hh : c = K.holds
  · rw [if_pos hh] at declared
    cases declared
    rw [hh]
    exact valid_holds laws read
  rw [if_neg hh] at declared
  by_cases hi : c = K.imp
  · rw [if_pos hi] at declared
    cases declared
    rw [hi]
    exact valid_imp laws read
  rw [if_neg hi] at declared
  cases carrier : K.quantifiers c with
  | some A =>
      rw [carrier] at declared
      cases declared
      exact valid_all laws read carrier
  | none =>
      rw [carrier] at declared
      cases equation : K.equationCarrier c with
      | none => rw [equation] at declared; cases declared
      | some A =>
          rw [equation] at declared
          cases declared
          exact valid_eq laws read equation

end Laws

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
