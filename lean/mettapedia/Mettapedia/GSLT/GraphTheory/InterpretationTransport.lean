import Mettapedia.GSLT.GraphTheory.Interpretation
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Finset

/-!
# Coding equivalences and graph interpretation

A change of web representation must transport the coding function, not just
the carrier. The coding equation below derives transport of application,
abstraction, and the interpretation of every lambda term.
-/

namespace Mettapedia.GSLT.GraphTheory

open Mettapedia.GSLT.Core

/-- An equivalence of webs respecting their actual finite-input coding. -/
structure CodingEquiv (D E : GraphModel) where
  carrier : D.Carrier ≃ E.Carrier
  code_map (a : Finset D.Carrier) (x : D.Carrier) :
    carrier (D.code a x) = E.code (carrier.finsetCongr a) (carrier x)

namespace CodingEquiv

variable {D E F : GraphModel}

def refl (D : GraphModel) : CodingEquiv D D where
  carrier := Equiv.refl _
  code_map a x := by simp

def symm (e : CodingEquiv D E) : CodingEquiv E D where
  carrier := e.carrier.symm
  code_map a x := by
    apply e.carrier.injective
    rw [e.carrier.apply_symm_apply, e.code_map, e.carrier.apply_symm_apply]
    change E.code a x = E.code (e.carrier.finsetCongr (e.carrier.finsetCongr.symm a)) x
    rw [Equiv.apply_symm_apply]

def trans (e : CodingEquiv D E) (f : CodingEquiv E F) : CodingEquiv D F where
  carrier := e.carrier.trans f.carrier
  code_map a x := by
    change f.carrier (e.carrier (D.code a x)) = _
    rw [e.code_map, f.code_map]
    rw [← Equiv.finsetCongr_trans]
    rfl

@[ext] theorem ext {e f : CodingEquiv D E} (h : e.carrier = f.carrier) : e = f := by
  cases e
  cases f
  cases h
  rfl

@[simp] theorem refl_trans (e : CodingEquiv D E) : (refl D).trans e = e := by
  ext x
  rfl

@[simp] theorem trans_refl (e : CodingEquiv D E) : e.trans (refl E) = e := by
  ext x
  rfl

theorem trans_assoc {G : GraphModel} (e : CodingEquiv D E)
    (f : CodingEquiv E F) (g : CodingEquiv F G) :
    (e.trans f).trans g = e.trans (f.trans g) := by
  ext x
  rfl

@[simp] theorem symm_trans (e : CodingEquiv D E) : e.symm.trans e = refl E := by
  ext x
  exact e.carrier.apply_symm_apply x

@[simp] theorem trans_symm (e : CodingEquiv D E) : e.trans e.symm = refl D := by
  ext x
  exact e.carrier.symm_apply_apply x

/-- The existing powerset equivalence induced by the web equivalence. -/
def sets (e : CodingEquiv D E) : Set D.Carrier ≃ Set E.Carrier :=
  Equiv.Set.congr e.carrier

@[simp] theorem sets_apply (e : CodingEquiv D E) (s : Set D.Carrier) :
    e.sets s = e.carrier '' s := rfl

@[simp] theorem sets_symm (e : CodingEquiv D E) : e.symm.sets = e.sets.symm := rfl

@[simp] theorem sets_trans (e : CodingEquiv D E) (f : CodingEquiv E F)
    (s : Set D.Carrier) : (e.trans f).sets s = f.sets (e.sets s) := by
  simp only [sets_apply, Set.image_image]
  rfl

@[simp] theorem sets_finset (e : CodingEquiv D E) (a : Finset D.Carrier) :
    e.sets (↑a : Set D.Carrier) = (↑(e.carrier.finsetCongr a) : Set E.Carrier) := by
  ext x
  simp [Equiv.finsetCongr_apply]

theorem sets_mono (e : CodingEquiv D E) {a b : Set D.Carrier} (h : a ⊆ b) :
    e.sets a ⊆ e.sets b := Set.image_mono h

theorem application_subset (e : CodingEquiv D E) (fn arg : Set D.Carrier) :
    e.sets (D.apply fn arg) ⊆ E.apply (e.sets fn) (e.sets arg) := by
  rintro _ ⟨x, ⟨a, ha, hx⟩, rfl⟩
  refine ⟨e.carrier.finsetCongr a, ?_, ?_⟩
  · rw [← e.sets_finset]
    exact e.sets_mono ha
  · rw [← e.code_map]
    exact ⟨D.code a x, hx, rfl⟩

/-- Application is derived from coding coherence, including every finite input. -/
theorem application (e : CodingEquiv D E) (fn arg : Set D.Carrier) :
    e.sets (D.apply fn arg) = E.apply (e.sets fn) (e.sets arg) := by
  apply Set.Subset.antisymm (e.application_subset fn arg)
  have h := e.symm.application_subset (e.sets fn) (e.sets arg)
  have h' := e.sets_mono h
  simpa only [sets_symm, Equiv.symm_apply_apply, Equiv.apply_symm_apply] using h'

/-- Abstraction transport for pointwise-related semantic bodies. -/
theorem abstraction (e : CodingEquiv D E)
    (f : Set D.Carrier → Set D.Carrier) (g : Set E.Carrier → Set E.Carrier)
    (h : ∀ a, e.sets (f a) = g (e.sets a)) :
    e.sets (D.abstraction f) = E.abstraction g := by
  ext y
  constructor
  · rintro ⟨_, ⟨a, x, rfl, hx⟩, rfl⟩
    refine ⟨e.carrier.finsetCongr a, e.carrier x, e.code_map a x, ?_⟩
    rw [← e.sets_finset, ← h]
    exact ⟨x, hx, rfl⟩
  · rintro ⟨a, x, rfl, hx⟩
    let b := e.carrier.symm.finsetCongr a
    have hb : e.carrier.finsetCongr b = a := e.carrier.finsetCongr.apply_symm_apply a
    have hx' : e.carrier.symm x ∈ f (↑b : Set D.Carrier) := by
      have hh := h (↑b : Set D.Carrier)
      rw [e.sets_finset, hb] at hh
      rw [← hh] at hx
      simpa using hx
    refine ⟨D.code b (e.carrier.symm x), ⟨b, e.carrier.symm x, rfl, hx'⟩, ?_⟩
    rw [e.code_map, hb, e.carrier.apply_symm_apply]

/-- In particular, arbitrary bodies transport by conjugation of the powersets. -/
theorem abstraction_conjugate (e : CodingEquiv D E) (f : Set D.Carrier → Set D.Carrier) :
    e.sets (D.abstraction f) =
      E.abstraction (fun a => e.sets (f (e.sets.symm a))) := by
  apply e.abstraction
  intro a
  rw [Equiv.symm_apply_apply]

def env (e : CodingEquiv D E) (ρ : Env D) : Env E := fun n => e.sets (ρ n)

@[simp] theorem env_extend (e : CodingEquiv D E) (ρ : Env D) (a : Set D.Carrier) :
    e.env (ρ.extend a) = (e.env ρ).extend (e.sets a) := by
  funext n
  cases n <;> rfl

@[simp] theorem env_symm_env (e : CodingEquiv D E) (ρ : Env D) :
    e.symm.env (e.env ρ) = ρ := by
  funext n
  exact e.sets.symm_apply_apply _

@[simp] theorem env_env_symm (e : CodingEquiv D E) (ρ : Env E) :
    e.env (e.symm.env ρ) = ρ := by
  funext n
  exact e.sets.apply_symm_apply _

/-- The whole-term representation square follows structurally from the actual
coding equation; interpretation preservation is not a field of `CodingEquiv`. -/
theorem interpretation (e : CodingEquiv D E) (term : LambdaTerm) (ρ : Env D) :
    e.sets (interpret D ρ term) = interpret E (e.env ρ) term := by
  induction term generalizing ρ with
  | var n => rfl
  | app fn arg ihFn ihArg =>
      simp only [interpret, e.application, ihFn, ihArg]
  | lam body ih =>
      apply e.abstraction
      intro a
      rw [ih, e.env_extend]

theorem validates_iff (e : CodingEquiv D E) (eq : LambdaEq) :
    validates D eq ↔ validates E eq := by
  constructor
  · intro h ρ
    have hh := congrArg e.sets (h (e.symm.env ρ))
    simpa only [e.interpretation, e.env_env_symm] using hh
  · intro h ρ
    apply e.sets.injective
    rw [e.interpretation, e.interpretation]
    exact h _

theorem theoryOf_eq (e : CodingEquiv D E) : theoryOf D = theoryOf E := by
  ext eq
  exact e.validates_iff eq

theorem lambdaTheoryOf_eq (e : CodingEquiv D E) : lambdaTheoryOf D = lambdaTheoryOf E := by
  have h : (lambdaTheoryOf D).equations = (lambdaTheoryOf E).equations := e.theoryOf_eq
  cases hD : lambdaTheoryOf D
  cases hE : lambdaTheoryOf E
  congr
  simpa only [hD, hE] using h

end CodingEquiv

/-- Recoding the existing graph model along a web equivalence. Both finite
support and output are decoded before invoking the original coding function. -/
def recode (D : GraphModel) (W : Web) (e : D.Carrier ≃ W.carrier) : GraphModel where
  web := W
  coding := {
    code := fun input => e (D.code (e.symm.finsetCongr input.1) (e.symm input.2))
    injective := by
      intro a b h
      have hh := D.coding.injective (e.injective h)
      have hleft := e.symm.finsetCongr.injective (congrArg Prod.fst hh)
      have hright := e.symm.injective (congrArg Prod.snd hh)
      exact Prod.ext hleft hright }

/-- Every recoding comes with a derived lawful coding equivalence. -/
def recodeEquiv (D : GraphModel) (W : Web) (e : D.Carrier ≃ W.carrier) :
    CodingEquiv D (recode D W e) where
  carrier := e
  code_map a x := by
    change e (D.code a x) = e (D.code (e.finsetCongr.symm (e.finsetCongr a)) (e.symm (e x)))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end Mettapedia.GSLT.GraphTheory
