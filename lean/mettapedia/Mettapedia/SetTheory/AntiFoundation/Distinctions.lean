import Mettapedia.SetTheory.AntiFoundation.Denotations
import Mettapedia.GSLT.Core.NonFactorization

/-!
# What each view keeps

A coarser denotation factors through a finer one: the value the coarser view
assigns is a function of the finer value. Along the chain Boffa, Finsler,
Scott, Aczel, Foundation, each step forgets a distinction. The adjacent
fibres are finite pictures. Two pictures with the same coarser value and
different finer values are a non-trivial fibre. The empty picture is a
positive example: every view keeps it, and keeps it alone among the menu as
the empty set.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.AntiFoundation

open Mettapedia.GSLT.Core.NonFactorization

theorem factors_comp {A S M V : Type} {shadow : A → S} {mid : A → M} {invariant : A → V}
    (h1 : Factors shadow mid) (h2 : Factors mid invariant) : Factors shadow invariant := by
  obtain ⟨r1, hr1⟩ := h1
  obtain ⟨r2, hr2⟩ := h2
  exact ⟨fun s => r2 (r1 s), fun a => (congrArg r2 (hr1 a)).trans (hr2 a)⟩

def recoverFafaFromBafa : BSet → FSet
  | .atomA => .omega
  | .atomB => .omega
  | .cycL => .omega
  | .cycR => .omega
  | .empty => .empty
  | .nest => .nest
  | .self => .self
  | .f0 => .f0
  | .f1 => .f1
  | .f2 => .f2
  | .colT => .colT
  | .colS => .colS

def recoverSafaFromFafa : FSet → SSet
  | .empty => .empty
  | .omega => .omega
  | .nest => .nest
  | .self => .self
  | .f0 => .finT
  | .f1 => .finS
  | .f2 => .finS
  | .colT => .finT
  | .colS => .finS

def recoverAfaFromSafa : SSet → ASet
  | .empty => .empty
  | .nest => .nest
  | _ => .omega

def recoverFoundFromAfa : ASet → Option FoundSet
  | .empty => some .empty
  | _ => none

def recoverAfaFromFafa : FSet → ASet
  | .empty => .empty
  | .nest => .nest
  | _ => .omega

theorem factors_bafa_fafa : Factors denoteBAFA denoteFAFA :=
  ⟨recoverFafaFromBafa, fun p => by cases p <;> rfl⟩

theorem factors_fafa_safa : Factors denoteFAFA denoteSAFA :=
  ⟨recoverSafaFromFafa, fun p => by cases p <;> rfl⟩

theorem factors_safa_afa : Factors denoteSAFA denoteAFA :=
  ⟨recoverAfaFromSafa, fun p => by cases p <;> rfl⟩

theorem factors_afa_found : Factors denoteAFA denoteFoundation :=
  ⟨recoverFoundFromAfa, fun p => by cases p <;> rfl⟩

theorem factors_bafa_afa : Factors denoteBAFA denoteAFA :=
  factors_comp factors_bafa_fafa (factors_comp factors_fafa_safa factors_safa_afa)

/-- The nest and the loop are one refusal for Foundation, and two sets for Aczel. -/
def fiber_found_afa : NonTrivialFiber denoteFoundation denoteAFA where
  left := .nest
  right := .loopA
  sameShadow := rfl
  differentValue := by intro h; cases h

/-- The Scott nodes are one set for Aczel, and `Ω` against `{Ω, s}` for Scott. -/
def fiber_afa_safa : NonTrivialFiber denoteAFA denoteSAFA where
  left := .scott0
  right := .scott1
  sameShadow := rfl
  differentValue := by intro h; cases h

/-- The Finsler nodes `n1` and `n2` are one set for Scott and two sets for Finsler. -/
def fiber_safa_fafa : NonTrivialFiber denoteSAFA denoteFAFA where
  left := .fin1
  right := .fin2
  sameShadow := rfl
  differentValue := by intro h; cases h

/-- Two copies of the loop are one Quine atom for Finsler and two for Boffa. -/
def fiber_fafa_bafa : NonTrivialFiber denoteFAFA denoteBAFA where
  left := .loopA
  right := .loopB
  sameShadow := rfl
  differentValue := by intro h; cases h

/-- The two-cycle is one Quine atom for Finsler and an exact picture for Boffa. -/
def fiber_fafa_bafa_cycle : NonTrivialFiber denoteFAFA denoteBAFA where
  left := .cycL
  right := .cycR
  sameShadow := rfl
  differentValue := by intro h; cases h

theorem denoteAFA_of_fafa (p : Pic) : denoteAFA p = recoverAfaFromFafa (denoteFAFA p) := by
  cases p <;> rfl

/-- The two loops remain a fibre after the Finsler value is forgotten down to Aczel. -/
def fiber_afa_bafa : NonTrivialFiber denoteAFA denoteBAFA :=
  NonTrivialFiber.coarsen denoteAFA_of_fafa fiber_fafa_bafa

theorem not_factors_found_afa : ¬ Factors denoteFoundation denoteAFA :=
  fiber_found_afa.not_factors

theorem not_factors_afa_safa : ¬ Factors denoteAFA denoteSAFA :=
  fiber_afa_safa.not_factors

theorem not_factors_safa_fafa : ¬ Factors denoteSAFA denoteFAFA :=
  fiber_safa_fafa.not_factors

theorem not_factors_fafa_bafa : ¬ Factors denoteFAFA denoteBAFA :=
  fiber_fafa_bafa.not_factors

theorem not_factors_afa_bafa : ¬ Factors denoteAFA denoteBAFA :=
  fiber_afa_bafa.not_factors

theorem all_agree_empty :
    denoteFoundation .empty = some .empty ∧ denoteAFA .empty = .empty ∧
      denoteSAFA .empty = .empty ∧ denoteFAFA .empty = .empty ∧
      denoteBAFA .empty = .empty :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end Mettapedia.SetTheory.AntiFoundation
