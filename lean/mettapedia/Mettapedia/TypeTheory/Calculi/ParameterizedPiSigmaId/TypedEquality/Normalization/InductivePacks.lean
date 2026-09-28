import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Definition

/-!
# Reducibility at simple inductive types

The reducible terms of a simple inductive type are defined by a mutual
induction over their weak-head normal forms and the arguments of
constructors. Every property of them follows from the corresponding property
of the packs of the closed field types, by the same mutual induction:
reflexivity, the two ends of an equality, symmetry, transitivity, transport to
other packs, renaming and expansion. The facts about the field packs are
hypotheses, so this module does not depend on how those packs arise.

Weak-head normal forms are unique and a constructor names its fields, so the
normal forms of a middle term agree in transitivity.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-- A closed field type of one of the constructors. -/
def IsClosedField (ctors : List (DeclName × List (Field Head))) (F : Tm Head 0) : Prop :=
  ∃ k fields, (k, fields) ∈ ctors ∧ Field.closed F ∈ fields

theorem IsClosedField.of_mem {ctors : List (DeclName × List (Field Head))} {k : DeclName}
    {fields : List (Field Head)} (mem : (k, fields) ∈ ctors) {F : Tm Head 0}
    (closed : Field.closed F ∈ fields) : IsClosedField ctors F :=
  ⟨k, fields, mem, closed⟩

variable {S : Setting Head L} {n : Nat} {Γ : Ctx Head n} {T : DeclName}
  {ctors : List (DeclName × List (Field Head))}

/-! ## Normal forms -/

/-- A constructor spine of an inductive type is canonical. -/
theorem ctorSpine_canonical (role : S.roles T = .inductive ctors) {k : DeclName}
    {fields : List (Field Head)} (mem : (k, fields) ∈ ctors) (args : List (Tm Head n)) :
    Canonical S.roles (appSpine (.const k) args) :=
  .inr ⟨k, _, args, S.constructors.arity role mem, rfl⟩

/-- The two shapes of a reducible normal form of an inductive type. -/
theorem IndNf.shape {fieldPack : Tm Head 0 → Pack Head n} {nf : Tm Head n}
    (normal : IndNf S Γ T ctors fieldPack nf) :
    (∃ k fields args, (k, fields) ∈ ctors ∧ IndFields S Γ T ctors fieldPack fields args ∧
        nf = appSpine (.const k) args) ∨
      (Neutral S.roles nf ∧ S.E.convNe Γ nf nf (.const T)) := by
  cases normal with
  | ctor mem arguments => exact .inl ⟨_, _, _, mem, arguments, rfl⟩
  | neutral neutral conv => exact .inr ⟨neutral, conv⟩

theorem IndNf.whnf (role : S.roles T = .inductive ctors) {fieldPack : Tm Head 0 → Pack Head n}
    {nf : Tm Head n} (normal : IndNf S Γ T ctors fieldPack nf) : Whnf S.R S.roles nf := by
  cases normal with
  | ctor mem _ => exact canonical_whnf S.shape (ctorSpine_canonical role mem _)
  | neutral neutral _ => exact neutral.whnf S.shape

theorem IndEqNf.whnf (role : S.roles T = .inductive ctors) {fieldPack : Tm Head 0 → Pack Head n}
    {nf nf' : Tm Head n} (normal : IndEqNf S Γ T ctors fieldPack nf nf') :
    Whnf S.R S.roles nf ∧ Whnf S.R S.roles nf' := by
  cases normal with
  | ctor mem _ =>
      exact ⟨canonical_whnf S.shape (ctorSpine_canonical role mem _),
        canonical_whnf S.shape (ctorSpine_canonical role mem _)⟩
  | neutral neutral neutral' _ => exact ⟨neutral.whnf S.shape, neutral'.whnf S.shape⟩

/-! ## Reflexivity -/

section Reflexivity

variable {fieldPack : Tm Head 0 → Pack Head n}

mutual

theorem IndRedTm.refl
    (fieldRefl : ∀ {F}, IsClosedField ctors F → ∀ {a}, (fieldPack F).redTm a →
      (fieldPack F).eqTm a a) :
    ∀ {t : Tm Head n}, IndRedTm S Γ T ctors fieldPack t → IndEqTm S Γ T ctors fieldPack t t
  | _, .mk red conv normal => .mk red red conv (IndNf.refl fieldRefl normal)

theorem IndNf.refl
    (fieldRefl : ∀ {F}, IsClosedField ctors F → ∀ {a}, (fieldPack F).redTm a →
      (fieldPack F).eqTm a a) :
    ∀ {nf : Tm Head n}, IndNf S Γ T ctors fieldPack nf → IndEqNf S Γ T ctors fieldPack nf nf
  | _, .ctor mem arguments =>
      .ctor mem (IndFields.refl fieldRefl (IsClosedField.of_mem mem) arguments)
  | _, .neutral neutral conv => .neutral neutral neutral conv

theorem IndFields.refl
    (fieldRefl : ∀ {F}, IsClosedField ctors F → ∀ {a}, (fieldPack F).redTm a →
      (fieldPack F).eqTm a a) :
    ∀ {fields : List (Field Head)} {args : List (Tm Head n)},
      (∀ {F}, Field.closed F ∈ fields → IsClosedField ctors F) →
      IndFields S Γ T ctors fieldPack fields args →
      IndEqFields S Γ T ctors fieldPack fields args args
  | _, _, _, .nil => .nil
  | _, _, sub, .recursive head tail =>
      .recursive (IndRedTm.refl fieldRefl head)
        (IndFields.refl fieldRefl (fun c => sub (List.mem_cons_of_mem _ c)) tail)
  | _, _, sub, .closed head tail =>
      .closed (fieldRefl (sub (List.mem_cons_self ..)) head)
        (IndFields.refl fieldRefl (fun c => sub (List.mem_cons_of_mem _ c)) tail)

end

end Reflexivity

/-! ## The two ends of an equality -/

section Ends

variable {fieldPack : Tm Head 0 → Pack Head n}

mutual

theorem IndEqTm.ends (laws : S.E.Laws S.R S.roles)
    (fieldEnds : ∀ {F}, IsClosedField ctors F → ∀ {a b}, (fieldPack F).eqTm a b →
      (fieldPack F).redTm a ∧ (fieldPack F).redTm b) :
    ∀ {t t' : Tm Head n}, IndEqTm S Γ T ctors fieldPack t t' →
      IndRedTm S Γ T ctors fieldPack t ∧ IndRedTm S Γ T ctors fieldPack t'
  | _, _, .mk red red' conv normal =>
      have normals := IndEqNf.ends laws fieldEnds normal
      ⟨.mk red (laws.convTm_trans conv (laws.convTm_symm conv)) normals.1,
        .mk red' (laws.convTm_trans (laws.convTm_symm conv) conv) normals.2⟩

theorem IndEqNf.ends (laws : S.E.Laws S.R S.roles)
    (fieldEnds : ∀ {F}, IsClosedField ctors F → ∀ {a b}, (fieldPack F).eqTm a b →
      (fieldPack F).redTm a ∧ (fieldPack F).redTm b) :
    ∀ {nf nf' : Tm Head n}, IndEqNf S Γ T ctors fieldPack nf nf' →
      IndNf S Γ T ctors fieldPack nf ∧ IndNf S Γ T ctors fieldPack nf'
  | _, _, .ctor mem arguments =>
      have args := IndEqFields.ends laws fieldEnds (IsClosedField.of_mem mem) arguments
      ⟨.ctor mem args.1, .ctor mem args.2⟩
  | _, _, .neutral neutral neutral' conv =>
      ⟨.neutral neutral (laws.convNe_trans conv (laws.convNe_symm conv)),
        .neutral neutral' (laws.convNe_trans (laws.convNe_symm conv) conv)⟩

theorem IndEqFields.ends (laws : S.E.Laws S.R S.roles)
    (fieldEnds : ∀ {F}, IsClosedField ctors F → ∀ {a b}, (fieldPack F).eqTm a b →
      (fieldPack F).redTm a ∧ (fieldPack F).redTm b) :
    ∀ {fields : List (Field Head)} {args args' : List (Tm Head n)},
      (∀ {F}, Field.closed F ∈ fields → IsClosedField ctors F) →
      IndEqFields S Γ T ctors fieldPack fields args args' →
      IndFields S Γ T ctors fieldPack fields args ∧ IndFields S Γ T ctors fieldPack fields args'
  | _, _, _, _, .nil => ⟨.nil, .nil⟩
  | _, _, _, sub, .recursive head tail =>
      have h := IndEqTm.ends laws fieldEnds head
      have t := IndEqFields.ends laws fieldEnds (fun c => sub (List.mem_cons_of_mem _ c)) tail
      ⟨.recursive h.1 t.1, .recursive h.2 t.2⟩
  | _, _, _, sub, .closed head tail =>
      have h := fieldEnds (sub (List.mem_cons_self ..)) head
      have t := IndEqFields.ends laws fieldEnds (fun c => sub (List.mem_cons_of_mem _ c)) tail
      ⟨.closed h.1 t.1, .closed h.2 t.2⟩

end

end Ends

/-! ## Symmetry -/

section Symmetry

variable {fieldPack : Tm Head 0 → Pack Head n}

mutual

theorem IndEqTm.symm (laws : S.E.Laws S.R S.roles)
    (fieldSymm : ∀ {F}, IsClosedField ctors F → ∀ {a b}, (fieldPack F).eqTm a b →
      (fieldPack F).eqTm b a) :
    ∀ {t t' : Tm Head n}, IndEqTm S Γ T ctors fieldPack t t' →
      IndEqTm S Γ T ctors fieldPack t' t
  | _, _, .mk red red' conv normal =>
      .mk red' red (laws.convTm_symm conv) (IndEqNf.symm laws fieldSymm normal)

theorem IndEqNf.symm (laws : S.E.Laws S.R S.roles)
    (fieldSymm : ∀ {F}, IsClosedField ctors F → ∀ {a b}, (fieldPack F).eqTm a b →
      (fieldPack F).eqTm b a) :
    ∀ {nf nf' : Tm Head n}, IndEqNf S Γ T ctors fieldPack nf nf' →
      IndEqNf S Γ T ctors fieldPack nf' nf
  | _, _, .ctor mem arguments =>
      .ctor mem (IndEqFields.symm laws fieldSymm (IsClosedField.of_mem mem) arguments)
  | _, _, .neutral neutral neutral' conv => .neutral neutral' neutral (laws.convNe_symm conv)

theorem IndEqFields.symm (laws : S.E.Laws S.R S.roles)
    (fieldSymm : ∀ {F}, IsClosedField ctors F → ∀ {a b}, (fieldPack F).eqTm a b →
      (fieldPack F).eqTm b a) :
    ∀ {fields : List (Field Head)} {args args' : List (Tm Head n)},
      (∀ {F}, Field.closed F ∈ fields → IsClosedField ctors F) →
      IndEqFields S Γ T ctors fieldPack fields args args' →
      IndEqFields S Γ T ctors fieldPack fields args' args
  | _, _, _, _, .nil => .nil
  | _, _, _, sub, .recursive head tail =>
      .recursive (IndEqTm.symm laws fieldSymm head)
        (IndEqFields.symm laws fieldSymm (fun c => sub (List.mem_cons_of_mem _ c)) tail)
  | _, _, _, sub, .closed head tail =>
      .closed (fieldSymm (sub (List.mem_cons_self ..)) head)
        (IndEqFields.symm laws fieldSymm (fun c => sub (List.mem_cons_of_mem _ c)) tail)

end

end Symmetry

/-! ## Transitivity -/

section Transitivity

variable {fieldPack : Tm Head 0 → Pack Head n}

mutual

theorem IndEqTm.trans (laws : S.E.Laws S.R S.roles) (role : S.roles T = .inductive ctors)
    (fieldTrans : ∀ {F}, IsClosedField ctors F → ∀ {a b c}, (fieldPack F).eqTm a b →
      (fieldPack F).eqTm b c → (fieldPack F).eqTm a c) :
    ∀ {t t' t'' : Tm Head n}, IndEqTm S Γ T ctors fieldPack t t' →
      IndEqTm S Γ T ctors fieldPack t' t'' → IndEqTm S Γ T ctors fieldPack t t''
  | _, _, _, .mk red red' conv normal, .mk red₂ red₂' conv₂ normal₂ => by
      have same := WhRed.whnf_unique S.shape red'.red red₂.red (IndEqNf.whnf role normal).2
        (IndEqNf.whnf role normal₂).1
      exact .mk red red₂' (laws.convTm_trans conv (by rw [same]; exact conv₂))
        (IndEqNf.trans laws role fieldTrans normal normal₂ same)

theorem IndEqNf.trans (laws : S.E.Laws S.R S.roles) (role : S.roles T = .inductive ctors)
    (fieldTrans : ∀ {F}, IsClosedField ctors F → ∀ {a b c}, (fieldPack F).eqTm a b →
      (fieldPack F).eqTm b c → (fieldPack F).eqTm a c) :
    ∀ {a b b' c : Tm Head n}, IndEqNf S Γ T ctors fieldPack a b →
      IndEqNf S Γ T ctors fieldPack b' c → b = b' → IndEqNf S Γ T ctors fieldPack a c
  | _, _, _, _, .ctor mem arguments, .ctor mem' arguments', same => by
      have heads := appSpine_const_injective same
      have sameFields := S.constructors.fields_unique role mem (by rw [heads.1]; exact mem')
      have result := IndEqFields.trans laws role fieldTrans (IsClosedField.of_mem mem)
        arguments arguments' sameFields heads.2
      rw [← heads.1]
      exact .ctor mem result
  | _, _, _, _, .ctor mem _, .neutral neutral _ _, same =>
      (neutral.not_canonical (by rw [← same]; exact ctorSpine_canonical role mem _)).elim
  | _, _, _, _, .neutral _ neutral' _, .ctor mem _, same =>
      (neutral'.not_canonical (by rw [same]; exact ctorSpine_canonical role mem _)).elim
  | _, _, _, _, .neutral neutral _ conv, .neutral _ neutral₂' conv₂, same =>
      .neutral neutral neutral₂' (laws.convNe_trans conv (by rw [same]; exact conv₂))

theorem IndEqFields.trans (laws : S.E.Laws S.R S.roles) (role : S.roles T = .inductive ctors)
    (fieldTrans : ∀ {F}, IsClosedField ctors F → ∀ {a b c}, (fieldPack F).eqTm a b →
      (fieldPack F).eqTm b c → (fieldPack F).eqTm a c) :
    ∀ {fields fields' : List (Field Head)} {args args' args'' args''' : List (Tm Head n)},
      (∀ {F}, Field.closed F ∈ fields → IsClosedField ctors F) →
      IndEqFields S Γ T ctors fieldPack fields args args' →
      IndEqFields S Γ T ctors fieldPack fields' args'' args''' →
      fields = fields' → args' = args'' → IndEqFields S Γ T ctors fieldPack fields args args'''
  | _, _, _, _, _, _, _, .nil, .nil, _, _ => .nil
  | _, _, _, _, _, _, sub, .recursive head tail, .recursive head' tail', sameFields,
      sameArgs => by
      obtain ⟨_, sameFields⟩ := List.cons.inj sameFields
      obtain ⟨sameHead, sameArgs⟩ := List.cons.inj sameArgs
      exact .recursive (IndEqTm.trans laws role fieldTrans head (by rw [sameHead]; exact head'))
        (IndEqFields.trans laws role fieldTrans (fun c => sub (List.mem_cons_of_mem _ c))
          tail tail' sameFields sameArgs)
  | _, _, _, _, _, _, sub, .closed head tail, .closed head' tail', sameFields, sameArgs => by
      obtain ⟨sameField, sameFields⟩ := List.cons.inj sameFields
      obtain ⟨sameHead, sameArgs⟩ := List.cons.inj sameArgs
      have sameF := Field.closed.inj sameField
      exact .closed (fieldTrans (sub (List.mem_cons_self ..)) head
          (by rw [sameHead, sameF]; exact head'))
        (IndEqFields.trans laws role fieldTrans (fun c => sub (List.mem_cons_of_mem _ c))
          tail tail' sameFields sameArgs)
  | _, _, _, _, _, _, _, .nil, .recursive _ _, sameFields, _ => nomatch sameFields
  | _, _, _, _, _, _, _, .nil, .closed _ _, sameFields, _ => nomatch sameFields
  | _, _, _, _, _, _, _, .recursive _ _, .nil, sameFields, _ => nomatch sameFields
  | _, _, _, _, _, _, _, .recursive _ _, .closed _ _, sameFields, _ => nomatch sameFields
  | _, _, _, _, _, _, _, .closed _ _, .nil, sameFields, _ => nomatch sameFields
  | _, _, _, _, _, _, _, .closed _ _, .recursive _ _, sameFields, _ => nomatch sameFields

end

end Transitivity

/-! ## Transport to other field packs -/

section Transport

variable {fieldPack fieldPack' : Tm Head 0 → Pack Head n}

mutual

theorem IndRedTm.transport
    (fieldRed : ∀ {F}, IsClosedField ctors F → ∀ {a}, (fieldPack F).redTm a →
      (fieldPack' F).redTm a) :
    ∀ {t : Tm Head n}, IndRedTm S Γ T ctors fieldPack t → IndRedTm S Γ T ctors fieldPack' t
  | _, .mk red conv normal => .mk red conv (IndNf.transport fieldRed normal)

theorem IndNf.transport
    (fieldRed : ∀ {F}, IsClosedField ctors F → ∀ {a}, (fieldPack F).redTm a →
      (fieldPack' F).redTm a) :
    ∀ {nf : Tm Head n}, IndNf S Γ T ctors fieldPack nf → IndNf S Γ T ctors fieldPack' nf
  | _, .ctor mem arguments =>
      .ctor mem (IndFields.transport fieldRed (IsClosedField.of_mem mem) arguments)
  | _, .neutral neutral conv => .neutral neutral conv

theorem IndFields.transport
    (fieldRed : ∀ {F}, IsClosedField ctors F → ∀ {a}, (fieldPack F).redTm a →
      (fieldPack' F).redTm a) :
    ∀ {fields : List (Field Head)} {args : List (Tm Head n)},
      (∀ {F}, Field.closed F ∈ fields → IsClosedField ctors F) →
      IndFields S Γ T ctors fieldPack fields args → IndFields S Γ T ctors fieldPack' fields args
  | _, _, _, .nil => .nil
  | _, _, sub, .recursive head tail =>
      .recursive (IndRedTm.transport fieldRed head)
        (IndFields.transport fieldRed (fun c => sub (List.mem_cons_of_mem _ c)) tail)
  | _, _, sub, .closed head tail =>
      .closed (fieldRed (sub (List.mem_cons_self ..)) head)
        (IndFields.transport fieldRed (fun c => sub (List.mem_cons_of_mem _ c)) tail)

end

mutual

theorem IndEqTm.transport
    (fieldEq : ∀ {F}, IsClosedField ctors F → ∀ {a b}, (fieldPack F).eqTm a b →
      (fieldPack' F).eqTm a b) :
    ∀ {t t' : Tm Head n}, IndEqTm S Γ T ctors fieldPack t t' →
      IndEqTm S Γ T ctors fieldPack' t t'
  | _, _, .mk red red' conv normal => .mk red red' conv (IndEqNf.transport fieldEq normal)

theorem IndEqNf.transport
    (fieldEq : ∀ {F}, IsClosedField ctors F → ∀ {a b}, (fieldPack F).eqTm a b →
      (fieldPack' F).eqTm a b) :
    ∀ {nf nf' : Tm Head n}, IndEqNf S Γ T ctors fieldPack nf nf' →
      IndEqNf S Γ T ctors fieldPack' nf nf'
  | _, _, .ctor mem arguments =>
      .ctor mem (IndEqFields.transport fieldEq (IsClosedField.of_mem mem) arguments)
  | _, _, .neutral neutral neutral' conv => .neutral neutral neutral' conv

theorem IndEqFields.transport
    (fieldEq : ∀ {F}, IsClosedField ctors F → ∀ {a b}, (fieldPack F).eqTm a b →
      (fieldPack' F).eqTm a b) :
    ∀ {fields : List (Field Head)} {args args' : List (Tm Head n)},
      (∀ {F}, Field.closed F ∈ fields → IsClosedField ctors F) →
      IndEqFields S Γ T ctors fieldPack fields args args' →
      IndEqFields S Γ T ctors fieldPack' fields args args'
  | _, _, _, _, .nil => .nil
  | _, _, _, sub, .recursive head tail =>
      .recursive (IndEqTm.transport fieldEq head)
        (IndEqFields.transport fieldEq (fun c => sub (List.mem_cons_of_mem _ c)) tail)
  | _, _, _, sub, .closed head tail =>
      .closed (fieldEq (sub (List.mem_cons_self ..)) head)
        (IndEqFields.transport fieldEq (fun c => sub (List.mem_cons_of_mem _ c)) tail)

end

end Transport

/-! ## Renaming -/

section Rename

variable {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} {fieldPack : Tm Head 0 → Pack Head n}
  {fieldPack' : Tm Head 0 → Pack Head m}

mutual

theorem IndRedTm.rename (laws : S.E.Laws S.R S.roles) (w : World S Γ Δ ρ)
    (fieldRed : ∀ {F}, IsClosedField ctors F → ∀ {a}, (fieldPack F).redTm a →
      (fieldPack' F).redTm (Presentation.rename ρ a)) :
    ∀ {t : Tm Head n}, IndRedTm S Γ T ctors fieldPack t →
      IndRedTm S Δ T ctors fieldPack' (Presentation.rename ρ t)
  | _, .mk red conv normal =>
      .mk (red.rename w.1) (laws.convTm_rename w.1 w.2 conv) (IndNf.rename laws w fieldRed normal)

theorem IndNf.rename (laws : S.E.Laws S.R S.roles) (w : World S Γ Δ ρ)
    (fieldRed : ∀ {F}, IsClosedField ctors F → ∀ {a}, (fieldPack F).redTm a →
      (fieldPack' F).redTm (Presentation.rename ρ a)) :
    ∀ {nf : Tm Head n}, IndNf S Γ T ctors fieldPack nf →
      IndNf S Δ T ctors fieldPack' (Presentation.rename ρ nf)
  | _, .ctor mem arguments => by
      rw [rename_appSpine]
      exact .ctor mem (IndFields.rename laws w fieldRed (IsClosedField.of_mem mem) arguments)
  | _, .neutral neutral conv => .neutral (neutral.rename ρ) (laws.convNe_rename w.1 w.2 conv)

theorem IndFields.rename (laws : S.E.Laws S.R S.roles) (w : World S Γ Δ ρ)
    (fieldRed : ∀ {F}, IsClosedField ctors F → ∀ {a}, (fieldPack F).redTm a →
      (fieldPack' F).redTm (Presentation.rename ρ a)) :
    ∀ {fields : List (Field Head)} {args : List (Tm Head n)},
      (∀ {F}, Field.closed F ∈ fields → IsClosedField ctors F) →
      IndFields S Γ T ctors fieldPack fields args →
      IndFields S Δ T ctors fieldPack' fields (args.map (Presentation.rename ρ))
  | _, _, _, .nil => .nil
  | _, _, sub, .recursive head tail =>
      .recursive (IndRedTm.rename laws w fieldRed head)
        (IndFields.rename laws w fieldRed (fun c => sub (List.mem_cons_of_mem _ c)) tail)
  | _, _, sub, .closed head tail =>
      .closed (fieldRed (sub (List.mem_cons_self ..)) head)
        (IndFields.rename laws w fieldRed (fun c => sub (List.mem_cons_of_mem _ c)) tail)

end

mutual

theorem IndEqTm.rename (laws : S.E.Laws S.R S.roles) (w : World S Γ Δ ρ)
    (fieldEq : ∀ {F}, IsClosedField ctors F → ∀ {a b}, (fieldPack F).eqTm a b →
      (fieldPack' F).eqTm (Presentation.rename ρ a) (Presentation.rename ρ b)) :
    ∀ {t t' : Tm Head n}, IndEqTm S Γ T ctors fieldPack t t' →
      IndEqTm S Δ T ctors fieldPack' (Presentation.rename ρ t) (Presentation.rename ρ t')
  | _, _, .mk red red' conv normal =>
      .mk (red.rename w.1) (red'.rename w.1) (laws.convTm_rename w.1 w.2 conv)
        (IndEqNf.rename laws w fieldEq normal)

theorem IndEqNf.rename (laws : S.E.Laws S.R S.roles) (w : World S Γ Δ ρ)
    (fieldEq : ∀ {F}, IsClosedField ctors F → ∀ {a b}, (fieldPack F).eqTm a b →
      (fieldPack' F).eqTm (Presentation.rename ρ a) (Presentation.rename ρ b)) :
    ∀ {nf nf' : Tm Head n}, IndEqNf S Γ T ctors fieldPack nf nf' →
      IndEqNf S Δ T ctors fieldPack' (Presentation.rename ρ nf) (Presentation.rename ρ nf')
  | _, _, .ctor mem arguments => by
      rw [rename_appSpine, rename_appSpine]
      exact .ctor mem (IndEqFields.rename laws w fieldEq (IsClosedField.of_mem mem) arguments)
  | _, _, .neutral neutral neutral' conv =>
      .neutral (neutral.rename ρ) (neutral'.rename ρ) (laws.convNe_rename w.1 w.2 conv)

theorem IndEqFields.rename (laws : S.E.Laws S.R S.roles) (w : World S Γ Δ ρ)
    (fieldEq : ∀ {F}, IsClosedField ctors F → ∀ {a b}, (fieldPack F).eqTm a b →
      (fieldPack' F).eqTm (Presentation.rename ρ a) (Presentation.rename ρ b)) :
    ∀ {fields : List (Field Head)} {args args' : List (Tm Head n)},
      (∀ {F}, Field.closed F ∈ fields → IsClosedField ctors F) →
      IndEqFields S Γ T ctors fieldPack fields args args' →
      IndEqFields S Δ T ctors fieldPack' fields (args.map (Presentation.rename ρ))
        (args'.map (Presentation.rename ρ))
  | _, _, _, _, .nil => .nil
  | _, _, _, sub, .recursive head tail =>
      .recursive (IndEqTm.rename laws w fieldEq head)
        (IndEqFields.rename laws w fieldEq (fun c => sub (List.mem_cons_of_mem _ c)) tail)
  | _, _, _, sub, .closed head tail =>
      .closed (fieldEq (sub (List.mem_cons_self ..)) head)
        (IndEqFields.rename laws w fieldEq (fun c => sub (List.mem_cons_of_mem _ c)) tail)

end

end Rename

/-! ## Appending an argument -/

section Snoc

variable {fieldPack : Tm Head 0 → Pack Head n}

/-- A reducible argument for one field. -/
def IndField (S : Setting Head L) (Γ : Ctx Head n) (T : DeclName)
    (ctors : List (DeclName × List (Field Head))) (fieldPack : Tm Head 0 → Pack Head n) :
    Field Head → Tm Head n → Prop
  | .recursive, a => IndRedTm S Γ T ctors fieldPack a
  | .closed F, a => (fieldPack F).redTm a

/-- Reducibly equal arguments for one field. -/
def IndEqField (S : Setting Head L) (Γ : Ctx Head n) (T : DeclName)
    (ctors : List (DeclName × List (Field Head))) (fieldPack : Tm Head 0 → Pack Head n) :
    Field Head → Tm Head n → Tm Head n → Prop
  | .recursive, a, a' => IndEqTm S Γ T ctors fieldPack a a'
  | .closed F, a, a' => (fieldPack F).eqTm a a'

theorem IndFields.snoc {f : Field Head} {a : Tm Head n}
    (last : IndField S Γ T ctors fieldPack f a) :
    ∀ {args : List (Tm Head n)} {fields : List (Field Head)},
      IndFields S Γ T ctors fieldPack fields args →
      IndFields S Γ T ctors fieldPack (fields ++ [f]) (args ++ [a])
  | [], _, h => by
      cases h
      cases f with
      | recursive => exact .recursive last .nil
      | closed F => exact .closed last .nil
  | _ :: _, _, h => by
      cases h with
      | recursive head tail => exact .recursive head (IndFields.snoc last tail)
      | closed head tail => exact .closed head (IndFields.snoc last tail)

theorem IndEqFields.snoc {f : Field Head} {a a' : Tm Head n}
    (last : IndEqField S Γ T ctors fieldPack f a a') :
    ∀ {args : List (Tm Head n)} {fields : List (Field Head)} {args' : List (Tm Head n)},
      IndEqFields S Γ T ctors fieldPack fields args args' →
      IndEqFields S Γ T ctors fieldPack (fields ++ [f]) (args ++ [a]) (args' ++ [a'])
  | [], _, _, h => by
      cases h
      cases f with
      | recursive => exact .recursive last .nil
      | closed F => exact .closed last .nil
  | _ :: _, _, _, h => by
      cases h with
      | recursive head tail => exact .recursive head (IndEqFields.snoc last tail)
      | closed head tail => exact .closed head (IndEqFields.snoc last tail)

theorem IndEqFields.length :
    ∀ {args : List (Tm Head n)} {fields : List (Field Head)} {args' : List (Tm Head n)},
      IndEqFields S Γ T ctors fieldPack fields args args' →
      args.length = fields.length ∧ args'.length = fields.length
  | [], _, _, h => by cases h; exact ⟨rfl, rfl⟩
  | _ :: _, _, _, h => by
      cases h with
      | recursive head tail =>
          have e := IndEqFields.length tail
          exact ⟨by simp [e.1], by simp [e.2]⟩
      | closed head tail =>
          have e := IndEqFields.length tail
          exact ⟨by simp [e.1], by simp [e.2]⟩

end Snoc

/-! ## Expansion -/

section Expansion

variable {fieldPack : Tm Head 0 → Pack Head n}

theorem IndRedTm.expand {t u : Tm Head n} (red : RedTm S.R S.roles Γ t u (.const T))
    (reducible : IndRedTm S Γ T ctors fieldPack u) : IndRedTm S Γ T ctors fieldPack t := by
  obtain ⟨red', conv, normal⟩ := reducible
  exact .mk (red.trans red') conv normal

theorem IndEqTm.expand {t t' u u' : Tm Head n} (redT : RedTm S.R S.roles Γ t t' (.const T))
    (redU : RedTm S.R S.roles Γ u u' (.const T)) (equal : IndEqTm S Γ T ctors fieldPack t' u') :
    IndEqTm S Γ T ctors fieldPack t u := by
  obtain ⟨r, r', conv, normal⟩ := equal
  exact .mk (redT.trans r) (redU.trans r') conv normal

end Expansion

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
