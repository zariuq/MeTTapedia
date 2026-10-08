import Mettapedia.GSLT.Core.ContextualLadderTerminal
import Mettapedia.GSLT.Core.ContextualTypeReindexingCoherence

/-!
# Finite telescopes in a dependent model

The telescope records actual repeated comprehension in a supplied CwF.
Its variables are actual sections. A finite array of typed values can be
checked against its dependent component types and assembled into a model
substitution. No interpretation of a source judgment is a model field.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualModelTelescopes

open Mettapedia.GSLT.Core.ContextualLadder

universe u v w w'

variable {C : CwfWithTerminal.{u, v, w, w'}}

/-- A value retains the actual type of its supplied section. -/
abbrev Value (C : Cwf.{u, v, w, w'}) (Γ : C.Ctx) :=
  Σ A : C.Ty Γ, C.Tm Γ A

namespace Value

variable {K : Cwf.{u, v, w, w'}}

def substitute {Γ Δ : K.Ctx} (value : Value K Γ) (σ : K.Sub Δ Γ) : Value K Δ :=
  ⟨K.tySub value.1 σ, K.tmSub value.2 σ⟩

theorem substitute_identity {Γ : K.Ctx} (value : Value K Γ) :
    substitute value (K.idS Γ) = value :=
  Sigma.ext (K.tySub_id value.1)
    ((heq_of_eq (K.tmSub_id value.2)).trans (cast_heq _ _))

theorem substitute_composition {Γ Δ Θ : K.Ctx} (value : Value K Γ)
    (σ : K.Sub Δ Γ) (τ : K.Sub Θ Δ) :
    substitute value (K.compS σ τ) = substitute (substitute value σ) τ :=
  Sigma.ext (K.tySub_comp value.1 σ τ) (TypeOver.tmSub_comp_heq value.2 σ τ)

/-- Equality checking supplies the type transport; incompatible values fail. -/
noncomputable def atType? {Γ : K.Ctx} (value : Value K Γ) (A : K.Ty Γ) :
    Option (K.Tm Γ A) := by
  classical
  exact if equal : value.1 = A then some (cast (congrArg (K.Tm Γ) equal) value.2) else none

@[simp] theorem atType?_supplied {Γ : K.Ctx} (A : K.Ty Γ) (term : K.Tm Γ A) :
    atType? (⟨A, term⟩ : Value K Γ) A = some term := by
  classical
  simp [atType?]

theorem atType?_cast {Γ : K.Ctx} (value : Value K Γ) (A : K.Ty Γ)
    (equal : value.1 = A) :
    atType? value A = some (cast (congrArg (K.Tm Γ) equal) value.2) := by
  classical
  simp [atType?, equal]

theorem atType?_none {Γ : K.Ctx} (value : Value K Γ) (A : K.Ty Γ)
    (different : value.1 ≠ A) : atType? value A = none := by
  classical
  simp [atType?, different]

theorem atType?_eq_some_iff {Γ : K.Ctx} (value : Value K Γ) (A : K.Ty Γ)
    (term : K.Tm Γ A) : atType? value A = some term ↔ value = ⟨A, term⟩ := by
  classical
  cases value with
  | mk actual value =>
      by_cases equal : actual = A
      · cases equal
        simp [atType?]
      · rw [atType?, dif_neg equal]
        constructor
        · intro impossible
          cases impossible
        · intro same
          exact False.elim (equal (congrArg Sigma.fst same))

end Value

/-- The index is the actual model context resulting from comprehension. -/
inductive Telescope (C : CwfWithTerminal.{u, v, w, w'}) :
    Nat → C.toCwf.Ctx → Type (max u w) where
  | nil : Telescope C 0 C.empty
  | snoc {n : Nat} {Γ : C.toCwf.Ctx} (previous : Telescope C n Γ)
      (A : C.toCwf.Ty Γ) : Telescope C (n + 1) (C.toCwf.ext Γ A)

/-- A scoped model context together with its independent telescope. -/
abbrev Context (C : CwfWithTerminal.{u, v, w, w'}) (n : Nat) :=
  Σ Γ : C.toCwf.Ctx, Telescope C n Γ

namespace Context

abbrev nil (C : CwfWithTerminal.{u, v, w, w'}) : Context C 0 := ⟨C.empty, .nil⟩

abbrev snoc {n : Nat} (Γ : Context C n) (A : C.toCwf.Ty Γ.1) : Context C (n + 1) :=
  ⟨C.toCwf.ext Γ.1 A, .snoc Γ.2 A⟩

end Context

namespace Telescope

variable {n : Nat} {Γ Δ Θ : C.toCwf.Ctx}

/-- The newest section is generic; older ones are genuinely weakened. -/
def lookup : {n : Nat} → {Γ : C.toCwf.Ctx} →
    Telescope C n Γ → Fin n → Value C.toCwf Γ
  | _, _, .nil, index => Fin.elim0 index
  | _, _, .snoc previous A, index =>
      Fin.cases ⟨C.toCwf.tySub A (C.toCwf.wk A), C.toCwf.vz A⟩
        (fun preceding => Value.substitute (lookup previous preceding) (C.toCwf.wk A)) index

@[simp] theorem variable_zero (previous : Telescope C n Γ) (A : C.toCwf.Ty Γ) :
    lookup (.snoc previous A) 0 =
      ⟨C.toCwf.tySub A (C.toCwf.wk A), C.toCwf.vz A⟩ := rfl

@[simp] theorem variable_succ (previous : Telescope C n Γ) (A : C.toCwf.Ty Γ)
    (index : Fin n) : lookup (.snoc previous A) index.succ =
      Value.substitute (lookup previous index) (C.toCwf.wk A) := rfl

/-- Read each supplied substitution through the actual telescope variables. -/
def components (telescope : Telescope C n Γ) (σ : C.toCwf.Sub Δ Γ) :
    Fin n → Value C.toCwf Δ := fun index => Value.substitute (lookup telescope index) σ

theorem components_composition (telescope : Telescope C n Γ)
    (σ : C.toCwf.Sub Δ Γ) (τ : C.toCwf.Sub Θ Δ) (index : Fin n) :
    components telescope (C.toCwf.compS σ τ) index =
      Value.substitute (components telescope σ index) τ :=
  Value.substitute_composition _ σ τ

@[simp] theorem components_succ (previous : Telescope C n Γ) (A : C.toCwf.Ty Γ)
    (σ : C.toCwf.Sub Δ (C.toCwf.ext Γ A)) (index : Fin n) :
    components (.snoc previous A) σ index.succ =
      components previous (C.toCwf.compS (C.toCwf.wk A) σ) index :=
  (Value.substitute_composition _ _ _).symm

theorem components_pair_zero (previous : Telescope C n Γ) (A : C.toCwf.Ty Γ)
    (σ : C.toCwf.Sub Δ Γ) (term : C.toCwf.Tm Δ (C.toCwf.tySub A σ)) :
    components (.snoc previous A) (C.toCwf.pair σ A term) 0 =
      ⟨C.toCwf.tySub A σ, term⟩ := by
  apply Sigma.ext
  · change C.toCwf.tySub (C.toCwf.tySub A (C.toCwf.wk A))
      (C.toCwf.pair σ A term) = C.toCwf.tySub A σ
    rw [← C.toCwf.tySub_comp, C.toCwf.wk_pair]
  · exact (heq_of_eq (C.toCwf.vz_pair σ A term)).trans (cast_heq _ _)

theorem components_pair_succ (previous : Telescope C n Γ) (A : C.toCwf.Ty Γ)
    (σ : C.toCwf.Sub Δ Γ) (term : C.toCwf.Tm Δ (C.toCwf.tySub A σ)) (index : Fin n) :
    components (.snoc previous A) (C.toCwf.pair σ A term) index.succ =
      components previous σ index := by
  rw [components_succ, C.toCwf.wk_pair]

/-- All finite dependent components are checked before the resulting arrow
is assembled. The empty telescope uses the chosen terminal map. -/
noncomputable def assemble? : {n : Nat} → {Γ : C.toCwf.Ctx} →
    Telescope C n Γ → (Fin n → Option (Value C.toCwf Δ)) →
      Option (C.toCwf.Sub Δ Γ)
  | _, _, .nil, _ => some (C.toEmpty Δ)
  | _, _, .snoc previous A, supplied =>
      match assemble? previous (fun index => supplied index.succ) with
      | none => none
      | some older =>
          match supplied 0 with
          | none => none
          | some value =>
              match Value.atType? value (C.toCwf.tySub A older) with
              | none => none
              | some term => some (C.toCwf.pair older A term)

/-- Reading and reassembling recovers the actual supplied model arrow. -/
theorem assemble?_components : {n : Nat} → {Γ : C.toCwf.Ctx} →
    (telescope : Telescope C n Γ) → (σ : C.toCwf.Sub Δ Γ) →
    assemble? telescope (fun index => some (components telescope σ index)) = some σ
  | _, _, .nil, σ => by
      simp only [assemble?]
      exact congrArg some (C.toEmpty_unique Δ σ).symm
  | _, _, .snoc previous A, σ => by
      have previousResult := assemble?_components previous (C.toCwf.compS (C.toCwf.wk A) σ)
      have previousInputs :
          (fun index => some (components (.snoc previous A) σ index.succ)) =
            (fun index => some (components previous (C.toCwf.compS (C.toCwf.wk A) σ) index)) := by
        funext index
        rw [components_succ]
      rw [assemble?, previousInputs, previousResult]
      simp only [components, variable_zero, Value.substitute]
      have equal : C.toCwf.tySub (C.toCwf.tySub A (C.toCwf.wk A)) σ =
          C.toCwf.tySub A (C.toCwf.compS (C.toCwf.wk A) σ) :=
        (C.toCwf.tySub_comp A _ _).symm
      rw [Value.atType?_cast _ _ equal]
      change some (C.toCwf.pair (C.toCwf.compS (C.toCwf.wk A) σ) A
        (cast (congrArg (C.toCwf.Tm Δ) equal) (C.toCwf.tmSub (C.toCwf.vz A) σ))) = some σ
      exact congrArg some (C.toCwf.pair_eta A σ)

/-- Successful checking returns exactly the supplied dependent components. -/
theorem assemble?_sound : {n : Nat} → {Γ : C.toCwf.Ctx} →
    (telescope : Telescope C n Γ) →
    (supplied : Fin n → Option (Value C.toCwf Δ)) → (σ : C.toCwf.Sub Δ Γ) →
    assemble? telescope supplied = some σ →
      ∀ index, supplied index = some (components telescope σ index)
  | _, _, .nil, _, _, _, index => Fin.elim0 index
  | _, _, .snoc previous A, supplied, σ, assembled, index => by
      cases earlier : assemble? previous (fun preceding => supplied preceding.succ) with
      | none => simp [assemble?, earlier] at assembled
      | some older =>
          cases newest : supplied 0 with
          | none => simp [assemble?, earlier, newest] at assembled
          | some value =>
              cases checked : Value.atType? value (C.toCwf.tySub A older) with
              | none => simp [assemble?, earlier, newest, checked] at assembled
              | some term =>
                  have assembledArrow : C.toCwf.pair older A term = σ := by
                    simpa only [assemble?, earlier, newest, checked, Option.some.injEq] using assembled
                  subst σ
                  cases index using Fin.cases with
                  | zero =>
                      rw [components_pair_zero, newest]
                      exact congrArg some ((Value.atType?_eq_some_iff _ _ _).mp checked)
                  | succ preceding =>
                      rw [components_pair_succ]
                      exact assemble?_sound previous _ older earlier preceding

theorem assemble?_eq_some_iff (telescope : Telescope C n Γ)
    (supplied : Fin n → Option (Value C.toCwf Δ)) (σ : C.toCwf.Sub Δ Γ) :
    assemble? telescope supplied = some σ ↔
      ∀ index, supplied index = some (components telescope σ index) := by
  constructor
  · exact assemble?_sound telescope supplied σ
  · intro all
    rw [funext all]
    exact assemble?_components telescope σ

/-- Checking already admitted arguments commutes with actual model
substitution. Failed checks need not remain failed after reindexing. -/
theorem assemble?_substitution (telescope : Telescope C n Γ)
    (supplied : Fin n → Option (Value C.toCwf Δ)) (σ : C.toCwf.Sub Δ Γ)
    (assembled : assemble? telescope supplied = some σ) (τ : C.toCwf.Sub Θ Δ) :
    assemble? telescope (fun index => (supplied index).map (fun value => value.substitute τ)) =
      some (C.toCwf.compS σ τ) := by
  apply (assemble?_eq_some_iff _ _ _).mpr
  intro index
  rw [assemble?_sound telescope supplied σ assembled index, Option.map_some,
    components_composition]

/-- The components of a model substitution determine it. -/
theorem components_injective (telescope : Telescope C n Γ) :
    Function.Injective (components (Δ := Δ) telescope) := by
  intro first second equal
  have results := congrArg (fun supplied => assemble? telescope (fun index => some (supplied index))) equal
  rw [assemble?_components, assemble?_components] at results
  exact Option.some.inj results

end Telescope

end Mettapedia.TypeTheory.ContextualModelTelescopes
