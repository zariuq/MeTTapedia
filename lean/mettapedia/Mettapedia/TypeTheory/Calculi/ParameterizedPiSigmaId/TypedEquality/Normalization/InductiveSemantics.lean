import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.InductiveDeclarations

/-!
# Semantics of simple inductive types

The constants of a declared simple inductive type are semantic.

- The type constant is a member of its universe: its closed field types are
  valid terms of the universe, hence reducible at the universe's level, and the
  type is reducible there with their packs.
- A constructor applied to reducible arguments for its fields is a reducible
  term of the type, in canonical form, so the constructor is semantic by
  passing from its full application to the constant one argument at a time.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (closeType applyClosed applyClosed_subst liftClosed_zero)

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

theorem ctorEntry_eq {T : DeclName} {fields : List (Field Head)} {j : Nat}
    (h : j < fields.length) : ctorEntry T fields j = liftClosed (fields[j].type T) := by
  simp [ctorEntry, h]

section Declaration

variable {R₀ R₁ R₂ : Rules Head} {T : DeclName} {u : Head}
  {ctors : List (DeclName × List (Field Head))} {rec : DeclName} {v : Head}
  (decl : DeclaresInductive S R₀ R₁ R₂ T u ctors rec v)
include decl

/-! ## The type constant -/

/-- The universe of the type is typed. -/
theorem DeclaresInductive.universe_typed :
    ∃ w, S.R.isUniverse w ∧ Typed S.R .nil (.head u) (.head w) := by
  obtain ⟨w, hw, typing, _⟩ := S.levels.successor decl.hu
  exact ⟨w, hw, .headType typing⟩

/-- The type constant is typed by its universe in every context. -/
theorem DeclaresInductive.typing {n : Nat} {Γ : Ctx Head n} :
    Typed S.R Γ (.const T) (.head u) := by
  obtain ⟨w, hw, typing⟩ := decl.universe_typed
  exact .const decl.declared typing hw

variable (laws : S.E.Laws S.R S.roles)
include laws

/-- The closed field types are valid terms of the universe. -/
theorem DeclaresInductive.field_valid {k : DeclName} {fields : List (Field Head)}
    {F : Tm Head 0} (mem : (k, fields) ∈ ctors) (closed : Field.closed F ∈ fields) :
    ValidTm S .nil F (.head u) :=
  Derivable.valid_sub laws decl.sub₀ (AllSemantic.semanticConstantsOf decl.semantic₀)
    (decl.fieldTyped mem closed) trivial

/-- In a formed context, the closed field types are reducible at the
universe's level with their packs `packOf`. -/
theorem DeclaresInductive.field_logRel {n : Nat} {Δ : Ctx Head n} (formed : CtxFormed S.R Δ)
    {k : DeclName} {fields : List (Field Head)} {F : Tm Head 0} (mem : (k, fields) ∈ ctors)
    (closed : Field.closed F ∈ fields) :
    LogRel S (S.levels.level u) Δ (liftClosed F) (packOf S Δ (liftClosed F)) := by
  obtain ⟨P, r⟩ := (decl.field_valid laws mem closed).logRel_at_level decl.hu
    (Δ := Δ) (σ := fun i => Fin.elim0 i) formed
  rw [subst_closed] at r
  exact r.packOf laws

/-- The inductive type, at its universe's level, in a formed context. -/
theorem DeclaresInductive.type_logRel {n : Nat} {Δ : Ctx Head n} (formed : CtxFormed S.R Δ) :
    LogRel S (S.levels.level u) Δ (.const T)
      (indPack S Δ T ctors fun F => packOf S Δ (liftClosed F)) :=
  .inductiveType (RedTy.refl ⟨u, decl.hu, decl.typing⟩) decl.role decl.typing decl.hu _
    fun mem closed => decl.field_logRel laws formed mem closed

theorem DeclaresInductive.type_reducible {n : Nat} {Δ : Ctx Head n} (formed : CtxFormed S.R Δ) :
    Reducible S Δ (.const T) (packOf S Δ (.const T)) :=
  (decl.type_logRel laws formed).reducible.packOf_self laws

/-- The pack of the inductive type in a formed context. -/
theorem DeclaresInductive.packOf_type {n : Nat} {Δ : Ctx Head n} (formed : CtxFormed S.R Δ) :
    packOf S Δ (.const T) = indPack S Δ T ctors fun F => packOf S Δ (liftClosed F) :=
  ((decl.type_logRel laws formed).reducible.eq_packOf laws).symm

/-- The type constant is semantic. -/
theorem DeclaresInductive.type_semantic : SemanticConstant S T (.head u) := by
  intro m Δ formed P r
  change Reducible S Δ (.head u) P at r
  rw [universe_pack laws decl.hu formed r]
  exact universe_member_intro decl.typing (laws.convTm_of_convNe
    (.inr (.inr ⟨T, ctors, decl.role, rfl⟩)) (.inr (.inr ⟨T, ctors, decl.role, rfl⟩))
    (laws.convNe_const T decl.typing))
    (.inr (.inr (.inr (.inr (.inr ⟨T, ctors, decl.role, rfl⟩))))) (decl.type_logRel laws formed)

/-- The constants of the first stage are semantic. -/
theorem DeclaresInductive.semantic₁ : AllSemantic S R₁ := by
  intro name type declared
  rcases decl.stage₁ declared with earlier | ⟨rfl, rfl⟩
  · exact decl.semantic₀ earlier
  · exact decl.type_semantic laws

/-! ## Constructors -/

/-- A valid substitution of a constructor's telescope gives reducible arguments
for its fields. -/
theorem DeclaresInductive.ctor_fields {m : Nat} {Δ : Ctx Head m} (formed : CtxFormed S.R Δ)
    {fields : List (Field Head)} :
    ∀ (j : Nat), j ≤ fields.length → ∀ {σ : Sub Head j m},
      ValidSubst S (ofEntries (ctorEntry T fields) j) Δ σ →
      IndFields S Δ T ctors (fun F => packOf S Δ (liftClosed F)) (fields.take j)
        (telescopeArgs (ofEntries (ctorEntry T fields) j) σ) := by
  intro j
  induction j with
  | zero => intro _ _ _; exact .nil
  | succ j ihj =>
      intro hj σ vσ
      obtain ⟨tail, P, r, h⟩ := vσ
      have ih := ihj (by omega) tail
      rw [telescopeArgs_ofEntries_succ, List.take_succ_eq_append_getElem (by omega)]
      refine IndFields.snoc ?_ ih
      rw [ctorEntry_eq (by omega), subst_liftClosed] at r
      rw [r.eq_packOf laws] at h
      have hf : fields[j] ∈ fields := List.getElem_mem (by omega)
      revert hf h r
      cases fields[j] with
      | recursive =>
          intro r h _
          change (packOf S Δ (.const T)).redTm (σ 0) at h
          rw [decl.packOf_type laws formed] at h
          exact h
      | closed F =>
          intro r h _
          exact h

/-- A validly equal pair of substitutions of a constructor's telescope gives
reducibly equal arguments for its fields. -/
theorem DeclaresInductive.ctor_fields_eq {m : Nat} {Δ : Ctx Head m} (formed : CtxFormed S.R Δ)
    {fields : List (Field Head)} :
    ∀ (j : Nat), j ≤ fields.length → ∀ {σ σ' : Sub Head j m},
      EqSubst S (ofEntries (ctorEntry T fields) j) Δ σ σ' →
      IndEqFields S Δ T ctors (fun F => packOf S Δ (liftClosed F)) (fields.take j)
        (telescopeArgs (ofEntries (ctorEntry T fields) j) σ)
        (telescopeArgs (ofEntries (ctorEntry T fields) j) σ') := by
  intro j
  induction j with
  | zero => intro _ _ _ _; exact .nil
  | succ j ihj =>
      intro hj σ σ' e
      obtain ⟨tail, P, r, h⟩ := e
      have ih := ihj (by omega) tail
      rw [telescopeArgs_ofEntries_succ, telescopeArgs_ofEntries_succ,
        List.take_succ_eq_append_getElem (by omega)]
      refine IndEqFields.snoc ?_ ih
      rw [ctorEntry_eq (by omega), subst_liftClosed] at r
      rw [r.eq_packOf laws] at h
      have hf : fields[j] ∈ fields := List.getElem_mem (by omega)
      revert hf h r
      cases fields[j] with
      | recursive =>
          intro r h _
          change (packOf S Δ (.const T)).eqTm (σ 0) (σ' 0) at h
          rw [decl.packOf_type laws formed] at h
          exact h
      | closed F =>
          intro r h _
          exact h

omit laws in
/-- A constructor at its declared type, in every context. -/
theorem DeclaresInductive.ctor_typing {k : DeclName} {fields : List (Field Head)}
    (mem : (k, fields) ∈ ctors) {n : Nat} {Γ : Ctx Head n} :
    Typed S.R Γ (.const k) (liftClosed (ctorType T fields)) := by
  obtain ⟨w, hw, typed⟩ := decl.ctorTyped mem
  exact .const (decl.ctorDeclared mem) (Derivable.mono decl.sub₁ typed) hw

/-- The full application of a constructor is valid in its telescope. -/
theorem DeclaresInductive.ctor_full {k : DeclName} {fields : List (Field Head)}
    (mem : (k, fields) ∈ ctors) :
    ValidTm S (ctorTele T fields) (applyClosed (ctorTele T fields) ids (.const k)) (.const T) := by
  have apply : ∀ {m : Nat} (σ : Sub Head fields.length m),
      Presentation.subst σ (applyClosed (ctorTele T fields) ids (.const k)) =
        applyClosed (ctorTele T fields) σ (.const k) := by
    intro m σ
    rw [applyClosed_subst]
    rfl
  refine ⟨⟨fun vσ => ⟨_, decl.type_reducible laws vσ.formed⟩, fun _ _ _ P r => ?_⟩,
    fun {m Δ σ} vσ P r => ?_, fun {m Δ σ σ'} vσ vσ' e P r => ?_⟩
  · exact r.reflexive.eqTy
  · have formed := vσ.formed
    change Reducible S Δ (.const T) P at r
    rw [apply, r.eq_packOf laws, decl.packOf_type laws formed]
    have typing := Typed.telescope_apply (vσ.substMor laws) (decl.ctor_typing mem (Γ := Δ))
    have spine := convNe_telescope_apply laws (Θ := ctorTele T fields) (X := .const T)
      (σ := σ) (τ := σ) (fun i => by
        obtain ⟨Q, rQ, hQ⟩ := vσ.lookup i
        exact ((rQ.escape laws).redTm hQ).2)
      (laws.convNe_const k (decl.ctor_typing mem))
    have args := decl.ctor_fields laws formed fields.length (Nat.le_refl _) vσ
    rw [List.take_length] at args
    rw [applyClosed_eq_appSpine] at typing spine ⊢
    exact .mk (RedTm.refl typing)
      (laws.convTm_of_convNe (.inr (.inl ⟨k, _, _, S.constructors.arity decl.role mem, rfl⟩))
        (.inr (.inl ⟨k, _, _, S.constructors.arity decl.role mem, rfl⟩)) spine) (.ctor mem args)
  · have formed := vσ.formed
    change Reducible S Δ (.const T) P at r
    rw [apply, apply, r.eq_packOf laws, decl.packOf_type laws formed]
    have typing := Typed.telescope_apply (vσ.substMor laws) (decl.ctor_typing mem (Γ := Δ))
    have typing' := Typed.telescope_apply (vσ'.substMor laws) (decl.ctor_typing mem (Γ := Δ))
    have spine := convNe_telescope_apply laws (Θ := ctorTele T fields) (X := .const T)
      (σ := σ) (τ := σ') (fun i => by
        obtain ⟨Q, rQ, eQ⟩ := e.lookup i
        exact (rQ.escape laws).eqTm eQ)
      (laws.convNe_const k (decl.ctor_typing mem))
    have args := decl.ctor_fields_eq laws formed fields.length (Nat.le_refl _) e
    rw [List.take_length] at args
    simp only [applyClosed_eq_appSpine] at typing typing' spine ⊢
    exact .mk (RedTm.refl typing) (RedTm.refl typing')
      (laws.convTm_of_convNe (.inr (.inl ⟨k, _, _, S.constructors.arity decl.role mem, rfl⟩))
        (.inr (.inl ⟨k, _, _, S.constructors.arity decl.role mem, rfl⟩)) spine)
      (.ctor mem args)

/-- Every constructor is semantic. -/
theorem DeclaresInductive.ctor_semantic {k : DeclName} {fields : List (Field Head)}
    (mem : (k, fields) ∈ ctors) : SemanticConstant S k (ctorType T fields) := by
  obtain ⟨w, hw, typed⟩ := decl.ctorTyped mem
  have validType : ValidTm S .nil (ctorType T fields) (.head w) :=
    Derivable.valid_sub laws decl.sub₁ (AllSemantic.semanticConstantsOf (decl.semantic₁ laws))
      typed trivial
  have typing : Typed S.R .nil (.const k) (closeType (ctorTele T fields) (.const T)) := by
    have h := decl.ctor_typing mem (Γ := .nil)
    rwa [liftClosed_zero] at h
  show SemanticConstant S k (closeType (ctorTele T fields) (.const T))
  exact SemanticConstant.of_telescope laws (.inl (S.constructors.arity decl.role mem))
    (Θ := ctorTele T fields) (C := .const T) typing (validType.validTy laws hw)
    (decl.ctor_full laws mem)

/-- The constants of the second stage are semantic. -/
theorem DeclaresInductive.semantic₂ : AllSemantic S R₂ := by
  intro name type declared
  rcases decl.stage₂ declared with earlier | ⟨fields, mem, rfl⟩
  · exact decl.semantic₁ laws earlier
  · exact decl.ctor_semantic laws mem

end Declaration

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
