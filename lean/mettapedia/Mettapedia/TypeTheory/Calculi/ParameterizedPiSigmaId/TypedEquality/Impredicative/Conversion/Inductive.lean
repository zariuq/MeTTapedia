import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Telescopes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Functions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Motives
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Recursor

/-!
# A simple inductive type in the conversion model

A simple inductive type `T` lists its constructors, each with fields that are `T` itself or a
closed type, and its recursor `rec` computes by one rule per constructor,
`rec P m₁ ⋯ m_c (kᵢ a₁ ⋯ aₐ) ⟶ mᵢ a₁ ⋯ aₐ (rec P m₁ ⋯ m_c aⱼ) ⋯`. This module gives its three
clauses in the conversion model, for every such type at once, as model SN has them
(`StrongNormalizationModel/Inductive.lean`):

* **the type** (`ValidTmN.inductiveType`): at every world `T` denotes its inductive pack, over
  the packs of its closed field types, and on the realizer side it is a type constant that the
  generic equality relates to itself;
* **the constructors** (`ValidTmN.inductiveCtor`): a constructor applied to related fields is
  related to itself applied to the other fields, and applied to realizers of the fields it is
  related, by the constructor candidate of every shape of the value, to itself applied to the
  other realizers;
* **the recursor** (`ValidTmN.inductiveRec`), with its motive into any universe. Its values are
  read on the value side, by induction on the inductive pack (`ValueSide.rec_related`, shared
  with model SN). Its realizers are proved by structural recursion on the shape of the
  scrutinee's value (`rec_claim`): realizers of a constructor shape reach that constructor
  with fields realizing the shapes of the fields, so both recursor applications reach, by typed
  reduction, the method's realizers applied to the fields and to the recursive calls, which
  the method's realizers relate one binder at a time (`method_app`); realizers that reach
  neutral terms leave both applications stuck on neutral spines, which the generic equality
  compares argument by argument (`rec_neutral`).

**What the type asks of the model.** On the value side, the type is inductive with the
constructors and the recursor computes by their rules (`ValueSide.InductiveValues`). On the
realizer side, the type is inductive with the same constructors, the type, the constructors
and the recursor are declared at their types (`DeclaresRecursor`), and the recursor's rules
are root steps.

Positive examples: the numbers are such a type, and every simple datatype declared over the
object package is another (`ExecutableModel.CodeModel.ConvRules.dataNewSoundN`). Negative
example: a relation that also related terms reaching no constructor, other than the neutral
ones, would leave the recursor's realizers stuck at them with no method to read; the clause of
a constructor candidate relates only terms reaching that constructor or neutral terms
(`ECand.ctorReal`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization hiding World Pack
open UniverseLevel (LevelOrder)
open Consistency (World Morph)
open Realizability (Daimonic)
open TelescopeAbstraction (closeType applyClosed applyClosed_subst liftClosed_zero)
open ValueSide (IndRel IndFields IndShape IndShapes HasIndShape HasIndShapes indPack closedFields
  InductiveValues FieldsV HypsV MethodsV mem_closedFields)

variable {Head L : Type} [LevelOrder L] {M : NModel Head L}

/-! ## Related values with related realizers -/

section Application

variable (laws : M.Laws)
include laws

/-- Related functions with related realizers, applied to related arguments with related
realizers, give related results with related realizers at a denotation of the codomain. -/
theorem DenN.pi_app_related {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : NPack M n} (den : DenN M ξ (.pi A B) P) {r : Nat}
    {Δ : Ctx Head r} (formed : CtxFormed M.side.R Δ) {X D : Tm Head r} {C : Tm Head (r + 1)}
    (hX : RedTy M.side.R M.side.roles Δ X (.pi D C)) {f f' a a' : Tm Head n}
    {t t' s s' : Tm Head r} (hf : P.Related f f' Δ X t t')
    (ha : ∀ {PA : NPack M n}, DenN M ξ A PA → PA.Related a a' Δ D s s') :
    ∃ PB : NPack M n, DenN M ξ (inst0 a B) PB ∧
      PB.Related (.app f a) (.app f' a') Δ (inst0 s C) (.app t s) (.app t' s') := by
  obtain ⟨PB, denB, rel⟩ := ValueSide.DenS.pi_app_exists laws.value den hf.1 fun d => (ha d).1
  exact ⟨PB, denB, rel, DenN.pi_app_real laws den formed hX hf.2
    (fun d => ⟨ValueSide.DenS.refl_left laws.value d (ha d).1, (ha d).2⟩) denB⟩

omit laws in
/-- A realizer type that is a dependent function type, at which a candidate relates two
terms, is reached by itself. -/
theorem redTy_pi_of_rel {r : Nat} {Δ : Ctx Head r} (formed : CtxFormed M.side.R Δ)
    (X : ECand M.side) {D : Tm Head r} {C : Tm Head (r + 1)} {t t' : Tm Head r}
    (h : X.rel Δ (.pi D C) t t') : RedTy M.side.R M.side.roles Δ (.pi D C) (.pi D C) :=
  RedTy.refl (Typed.isType (S := M.side.toSetting) (X.typed h).1 formed)

end Application

/-- The fields of a constructor, related at the denotations of their types, with realizers
related at the fields' types. -/
inductive FieldsN {n r : Nat} (ξ : World M.reading n) (Δ : Ctx Head r) (T : DeclName) :
    List (Field Head) → List (Tm Head n) → List (Tm Head n) → List (Tm Head r) →
      List (Tm Head r) → Prop where
  | nil : FieldsN ξ Δ T [] [] [] [] []
  | cons {f : Field Head} {a a' : Tm Head n} {u u' : Tm Head r} {fs : List (Field Head)}
      {as as' : List (Tm Head n)} {us us' : List (Tm Head r)} :
      (∀ {PA : NPack M n}, DenN M ξ (liftClosed (f.type T)) PA →
        PA.Related a a' Δ (liftClosed (f.type T)) u u') →
      FieldsN ξ Δ T fs as as' us us' →
      FieldsN ξ Δ T (f :: fs) (a :: as) (a' :: as') (u :: us) (u' :: us')

/-- The values of related fields with realizers are related fields. -/
theorem FieldsN.values {n r : Nat} {ξ : World M.reading n} {Δ : Ctx Head r} {T : DeclName} :
    ∀ {fs : List (Field Head)} {as as' : List (Tm Head n)} {us us' : List (Tm Head r)},
      FieldsN ξ Δ T fs as as' us us' → FieldsV ξ T fs as as'
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons h rest => .cons (fun d => (h d).1) (FieldsN.values rest)

/-- Induction hypotheses over the motive `P`, related at the motive at their value fields, with
realizers related at the realizer motive `p` at their realizer fields. -/
inductive HypsN {n r : Nat} (ξ : World M.reading n) (Δ : Ctx Head r) (P : Tm Head n)
    (p : Tm Head r) :
    List (Tm Head n) → List (Tm Head r) → List (Tm Head n) → List (Tm Head n) →
      List (Tm Head r) → List (Tm Head r) → Prop where
  | nil : HypsN ξ Δ P p [] [] [] [] [] []
  | cons {x ih ih' : Tm Head n} {x₀ ih₀ ih₀' : Tm Head r} {xs ihs ihs' : List (Tm Head n)}
      {xs₀ ihs₀ ihs₀' : List (Tm Head r)} :
      (∀ {R : NPack M n}, DenN M ξ (.app P x) R → R.Related ih ih' Δ (.app p x₀) ih₀ ih₀') →
      HypsN ξ Δ P p xs xs₀ ihs ihs' ihs₀ ihs₀' →
      HypsN ξ Δ P p (x :: xs) (x₀ :: xs₀) (ih :: ihs) (ih' :: ihs') (ih₀ :: ihs₀)
        (ih₀' :: ihs₀')

/-- The values of related hypotheses with realizers are related hypotheses. -/
theorem HypsN.values {n r : Nat} {ξ : World M.reading n} {Δ : Ctx Head r} {P : Tm Head n}
    {p : Tm Head r} :
    ∀ {xs : List (Tm Head n)} {xs₀ : List (Tm Head r)} {ihs ihs' : List (Tm Head n)}
      {ihs₀ ihs₀' : List (Tm Head r)}, HypsN ξ Δ P p xs xs₀ ihs ihs' ihs₀ ihs₀' →
        HypsV ξ P xs ihs ihs'
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, .cons h rest => .cons (fun d => (h d).1) (HypsN.values rest)

section Application

variable (laws : M.Laws)
include laws

/-- A function of the induction hypotheses, applied to related hypotheses with related
realizers. -/
theorem caseHyps_app {n r : Nat} {ξ : World M.reading n} {Δ : Ctx Head r}
    (formed : CtxFormed M.side.R Δ) {P target : Tm Head n} {p target₀ : Tm Head r} :
    ∀ {xs : List (Tm Head n)} {xs₀ : List (Tm Head r)} {ihs ihs' : List (Tm Head n)}
      {ihs₀ ihs₀' : List (Tm Head r)}, HypsN ξ Δ P p xs xs₀ ihs ihs' ihs₀ ihs₀' →
      ∀ {g g' : Tm Head n} {g₀ g₀' : Tm Head r} {PM : NPack M n},
        DenN M ξ (caseHyps P xs target) PM →
        PM.Related g g' Δ (caseHyps p xs₀ target₀) g₀ g₀' →
        ∃ R : NPack M n, DenN M ξ (.app P target) R ∧
          R.Related (appSpine g ihs) (appSpine g' ihs') Δ (.app p target₀)
            (appSpine g₀ ihs₀) (appSpine g₀' ihs₀')
  | _, _, _, _, _, _, .nil, g, g', g₀, g₀', PM, den, h => by
      rw [caseHyps_nil] at den h
      exact ⟨PM, den, h⟩
  | _, _, _, _, _, _, .cons (x := x) (x₀ := x₀) hx tail, g, g', g₀, g₀', PM, den, h => by
      rw [caseHyps_cons] at den h
      obtain ⟨PB, denB, hB⟩ := DenN.pi_app_related laws den formed
        (redTy_pi_of_rel formed (PM.real g) h.2) h hx
      rw [inst0_caseHyps] at denB hB
      exact caseHyps_app formed tail denB hB

/-- A method applied to related fields with related realizers, through the fields of its case
type. -/
theorem caseFields_app {n r : Nat} {ξ : World M.reading n} {Δ : Ctx Head r}
    (formed : CtxFormed M.side.R Δ) {T k : DeclName} :
    ∀ {fs : List (Field Head)} {as as' : List (Tm Head n)} {us us' : List (Tm Head r)},
      FieldsN ξ Δ T fs as as' us us' →
      ∀ {P : Tm Head n} {p : Tm Head r} {xs recs : List (Tm Head n)}
        {xs₀ recs₀ : List (Tm Head r)} {g g' : Tm Head n} {g₀ g₀' : Tm Head r}
        {PM : NPack M n}, DenN M ξ (caseFields T k fs P xs recs) PM →
        PM.Related g g' Δ (caseFields T k fs p xs₀ recs₀) g₀ g₀' →
        ∃ PH : NPack M n,
          DenN M ξ (caseHyps P (recs ++ recArgs fs as) (appSpine (.const k) (xs ++ as))) PH ∧
          PH.Related (appSpine g as) (appSpine g' as') Δ
            (caseHyps p (recs₀ ++ recArgs fs us) (appSpine (.const k) (xs₀ ++ us)))
            (appSpine g₀ us) (appSpine g₀' us')
  | _, _, _, _, _, .nil, P, p, xs, recs, xs₀, recs₀, g, g', g₀, g₀', PM, den, h => by
      simp only [caseFields, recArgs, List.append_nil] at den h ⊢
      exact ⟨PM, den, h⟩
  | .recursive :: fs, a :: as, _, u :: us, _, .cons ha tail, P, p, xs, recs, xs₀, recs₀,
      g, g', g₀, g₀', PM, den, h => by
      simp only [caseFields] at den h
      obtain ⟨PB, denB, hB⟩ := DenN.pi_app_related laws den formed
        (redTy_pi_of_rel formed (PM.real g) h.2) h ha
      rw [inst0_caseFields T k fs a P xs recs [.var 0] [a] rfl] at denB
      rw [inst0_caseFields T k fs u p xs₀ recs₀ [.var 0] [u] rfl] at hB
      obtain ⟨PH, denH, hH⟩ := caseFields_app formed tail denB hB
      simp only [List.append_assoc, List.singleton_append] at denH hH
      exact ⟨PH, denH, hH⟩
  | .closed F :: fs, a :: as, _, u :: us, _, .cons ha tail, P, p, xs, recs, xs₀, recs₀,
      g, g', g₀, g₀', PM, den, h => by
      simp only [caseFields] at den h
      obtain ⟨PB, denB, hB⟩ := DenN.pi_app_related laws den formed
        (redTy_pi_of_rel formed (PM.real g) h.2) h ha
      have inst := inst0_caseFields T k fs a P xs recs [] [] rfl
      have inst₀ := inst0_caseFields T k fs u p xs₀ recs₀ [] [] rfl
      rw [List.append_nil, List.append_nil] at inst inst₀
      rw [inst] at denB
      rw [inst₀] at hB
      obtain ⟨PH, denH, hH⟩ := caseFields_app formed tail denB hB
      simp only [List.append_assoc, List.singleton_append] at denH hH
      exact ⟨PH, denH, hH⟩

/-- **A method applied to related fields and hypotheses** with related realizers gives related
results with related realizers, at the motive at the constructor applied to the fields. -/
theorem method_app {n r : Nat} {ξ : World M.reading n} {Δ : Ctx Head r}
    (formed : CtxFormed M.side.R Δ) {T k : DeclName} {fs : List (Field Head)}
    {as as' : List (Tm Head n)} {us us' : List (Tm Head r)}
    (fields : FieldsN ξ Δ T fs as as' us us') {P : Tm Head n} {p : Tm Head r}
    {ihs ihs' : List (Tm Head n)} {ihs₀ ihs₀' : List (Tm Head r)}
    (hyps : HypsN ξ Δ P p (recArgs fs as) (recArgs fs us) ihs ihs' ihs₀ ihs₀')
    {g g' : Tm Head n} {g₀ g₀' : Tm Head r} {PM : NPack M n}
    (den : DenN M ξ (caseType T k fs P) PM)
    (hg : PM.Related g g' Δ (caseType T k fs p) g₀ g₀') :
    ∃ R : NPack M n, DenN M ξ (.app P (appSpine (.const k) as)) R ∧
      R.Related (appSpine g (as ++ ihs)) (appSpine g' (as' ++ ihs')) Δ
        (.app p (appSpine (.const k) us)) (appSpine g₀ (us ++ ihs₀))
        (appSpine g₀' (us' ++ ihs₀')) := by
  obtain ⟨PH, denH, hH⟩ := caseFields_app laws formed fields den hg
  simp only [List.nil_append] at denH hH
  obtain ⟨R, denR, hR⟩ := caseHyps_app laws formed hyps denH hH
  refine ⟨R, denR, ?_⟩
  rw [appSpine_append, appSpine_append, appSpine_append, appSpine_append]
  exact hR

end Application

/-! ## The type -/

/-- A valid closed type is a type of the realizer side. -/
theorem ValidTyN.isType_nil {A : Tm Head 0} (valid : ValidTyN M .nil A) :
    IsType M.side.R .nil A := by
  obtain ⟨-, -, -, types⟩ := valid (ξ := World.closed) (σ := fun i => Fin.elim0 i)
    (σ' := fun i => Fin.elim0 i) (Δ := .nil) (ς := fun i => Fin.elim0 i)
    (ς' := fun i => Fin.elim0 i) CtxFormed.nil
  have h := types.left
  rwa [show (fun i => Fin.elim0 i : Sub Head 0 0) = ids from funext fun i => Fin.elim0 i,
    subst_ids] at h

/-- **A simple inductive type is a valid term of its universe**: at every world it is
interpreted at the universe's level by its inductive pack, over the given packs of its closed
field types, and on the realizer side it is a type constant of an inductive type, typed at the
universe, that the generic equality relates to itself. -/
theorem ValidTmN.inductiveType (laws : M.Laws) {T : DeclName}
    {cs : List (DeclName × List (Field Head))} (role : M.roles T = .inductive cs)
    (realRole : M.side.roles T = .inductive cs) {u : Head} (hu : M.rules.isUniverse u)
    (realHu : M.side.R.isUniverse u) (declared : M.side.R.constantType T = some (.head u))
    (field : ∀ {m : Nat}, World M.reading m → Tm Head 0 → NPack M m)
    (fieldInterp : ∀ {m : Nat} (ξ : World M.reading m) {F : Tm Head 0}, F ∈ closedFields cs →
      NInterp M (M.levels.level u) ξ (liftClosed F) (field ξ F)) :
    ValidTmN M .nil (.const T) (.head u) := by
  refine ⟨ValidTyN.sort hu realHu, fun {m r ξ σ σ' Δ ς ς'} _ {P} den => ?_⟩
  rw [ValueSide.DenS.sort_inv laws.value hu den]
  have interp : ∀ {k : Nat} (ξ' : World M.reading k),
      NInterp M (M.levels.level u) ξ' (.const T) (indPack M.value T cs (field ξ')) :=
    fun ξ' => ValueSide.SInterp.ind .refl role (field ξ') fun hF => fieldInterp ξ' hF
  refine ⟨fun {_ ξ' _} _ => ⟨_, interp ξ', interp ξ', .const (.inr ⟨_, role⟩) .refl .refl⟩, ?_⟩
  obtain ⟨w, -, typingU, -⟩ := M.side.levels.successor realHu
  have typed : Typed M.side.R Δ (.const T) (.head u) :=
    .const declared (.headType typingU) (M.side.levels.universe_typing realHu typingU).1
  have form : IsTypeForm M.side.roles (.const T : Tm Head r) :=
    .inr (.inr (.inr (.inr (.inr ⟨T, _, realRole, rfl⟩))))
  exact ⟨⟨typed, typed, M.side.laws.convTm_of_convNe (.inr (.inr ⟨T, _, realRole, rfl⟩))
    (.inr (.inr ⟨T, _, realRole, rfl⟩)) (M.side.laws.convNe_const T typed)⟩,
    ⟨_, .refl typed, form⟩, ⟨_, .refl typed, form⟩⟩

/-! ## The constructors -/

/-- Related fields with related realizers, extended at the end. -/
theorem FieldsN.snoc {n r : Nat} {ξ : World M.reading n} {Δ : Ctx Head r} {T : DeclName} :
    ∀ {fs : List (Field Head)} {as as' : List (Tm Head n)} {us us' : List (Tm Head r)},
      FieldsN ξ Δ T fs as as' us us' → ∀ {f : Field Head} {a a' : Tm Head n} {u u' : Tm Head r},
      (∀ {PA : NPack M n}, DenN M ξ (liftClosed (f.type T)) PA →
        PA.Related a a' Δ (liftClosed (f.type T)) u u') →
      FieldsN ξ Δ T (fs ++ [f]) (as ++ [a]) (as' ++ [a']) (us ++ [u]) (us' ++ [u'])
  | _, _, _, _, _, .nil, _, _, _, _, _, h => .cons h .nil
  | _, _, _, _, _, .cons h₀ rest, _, _, _, _, _, h => .cons h₀ (FieldsN.snoc rest h)

/-- **Related valuations of a constructor's telescope relate its fields**, each at the
denotation of its type, with related realizers. -/
theorem EqSubstN.ctorFields (laws : M.Laws) {T : DeclName} {fs : List (Field Head)} :
    ∀ (j : Nat), j ≤ fs.length → ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head j m}
      {Δ : Ctx Head r} {ς ς' : Sub Head j r},
      EqSubstN M (ofEntries (ctorEntry T fs) j) ξ σ σ' Δ ς ς' →
      FieldsN ξ Δ T (fs.take j) (telescopeArgs (ofEntries (ctorEntry T fs) j) σ)
        (telescopeArgs (ofEntries (ctorEntry T fs) j) σ')
        (telescopeArgs (ofEntries (ctorEntry T fs) j) ς)
        (telescopeArgs (ofEntries (ctorEntry T fs) j) ς')
  | 0, _, _, _, _, _, _, _, _, _, _ => .nil
  | j + 1, hj, _, _, ξ, σ, σ', Δ, ς, ς', e => by
      obtain ⟨tail, P, denP, rel⟩ := e
      have rest := EqSubstN.ctorFields laws j (by omega) tail
      have entry : ∀ {k : Nat} (τ : Sub Head j k),
          Presentation.subst τ (ctorEntry T fs j) = liftClosed (fs[j].type T) := by
        intro k τ
        rw [ctorEntry, subst_liftClosed, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [entry] at denP rel
      rw [List.take_succ_eq_append_getElem (by omega)]
      exact FieldsN.snoc rest fun den => by
        rw [ValueSide.DenS.deterministic laws.value den denP]
        exact rel

section Fields

variable {n r : Nat} {ξ : World M.reading n} {Δ : Ctx Head r} {T : DeclName}
  {cs : List (DeclName × List (Field Head))} {field : Tm Head 0 → NPack M n}
  (hT : DenN M ξ (.const T) (indPack M.value T cs field))
  (hF : ∀ {F : Tm Head 0}, F ∈ closedFields cs → DenN M ξ (liftClosed F) (field F))
include hT hF

/-- Fields related at the denotations of their types are related at the inductive type's
fields. -/
theorem FieldsN.indFields :
    ∀ {fs : List (Field Head)} {as as' : List (Tm Head n)} {us us' : List (Tm Head r)},
      FieldsN ξ Δ T fs as as' us us' →
      (∀ {F : Tm Head 0}, Field.closed F ∈ fs → F ∈ closedFields cs) →
      IndFields M.value cs field fs as as'
  | _, _, _, _, _, .nil, _ => .nil
  | .recursive :: _, _, _, _, _, .cons h rest, closed =>
      .recursive (h hT).1 (FieldsN.indFields rest fun hF' => closed (List.mem_cons_of_mem _ hF'))
  | .closed _ :: _, _, _, _, _, .cons h rest, closed =>
      .closed (h (hF (closed List.mem_cons_self))).1
        (FieldsN.indFields rest fun hF' => closed (List.mem_cons_of_mem _ hF'))

/-- The realizers of related fields are related by the candidates of every shape of the
fields. -/
theorem FieldsN.reals :
    ∀ {fs : List (Field Head)} {as as' : List (Tm Head n)} {us us' : List (Tm Head r)}
      {fields : IndShapes Head n}, FieldsN ξ Δ T fs as as' us us' →
      HasIndShapes M.value cs fs as fields →
      (∀ {F : Tm Head 0}, Field.closed F ∈ fs → F ∈ closedFields cs) →
      FieldsRel T Δ (IndShapes.reals M.value T field fields) fs us us'
  | _, _, _, _, _, _, .nil, .nil, _ => .nil
  | .recursive :: _, _, _, _, _, _, .cons h rest, .recursive shape shapes, closed =>
      .cons ((h hT).2.2 ⟨_, shape⟩)
        (FieldsN.reals rest shapes fun hF' => closed (List.mem_cons_of_mem _ hF'))
  | .closed _ :: _, _, _, _, _, _, .cons h rest, .closed shapes, closed =>
      .cons (h (hF (closed List.mem_cons_self))).2
        (FieldsN.reals rest shapes fun hF' => closed (List.mem_cons_of_mem _ hF'))

end Fields

/-- **A constructor is a valid term of its declared type**: applied to related fields it is
related to itself applied to the other fields, by the clause of the constructor, and its
realizer instances, the constructor applied to related realizers of the fields, are related by
the constructor candidate of every shape of the value. The validity of the declared type and of
its parts are hypotheses, which the fundamental lemma of a smaller stage provides. -/
theorem ValidTmN.inductiveCtor (laws : M.Laws) {T : DeclName}
    {cs : List (DeclName × List (Field Head))} (role : M.roles T = .inductive cs)
    (realRole : M.side.roles T = .inductive cs) {k : DeclName} {fs : List (Field Head)}
    (mem : (k, fs) ∈ cs) (declared : M.side.R.constantType k = some (ctorType T fs))
    (validType : ValidTyN M .nil (ctorType T fs)) (partsType : StructuredN M .nil (ctorType T fs)) :
    ValidTmN M .nil (.const k) (ctorType T fs) := by
  obtain ⟨ctx, validResult, _⟩ :=
    ValidTyN.close_parts (ctorTele T fs) (C := .const T) validType partsType
  obtain ⟨w, hw, typedType⟩ := ValidTyN.isType_nil validType
  have typedK : ∀ {r : Nat} {Δ : Ctx Head r},
      Typed M.side.R Δ (.const k) (liftClosed (ctorType T fs)) :=
    .const declared typedType hw
  have typed : Typed M.side.R .nil (.const k) (ctorType T fs) := by
    have h := typedK (Δ := .nil)
    rwa [liftClosed_zero] at h
  have roleK : M.side.roles k = .constructor fs.length := M.side.constructors.arity realRole mem
  have typedApp : Typed M.side.R (ctorTele T fs) (applyClosed (ctorTele T fs) ids
      (liftClosed (.const k))) (.const T) := by
    have h := Typed.telescope_apply (X := .const T) (substMor_ids (ctorTele T fs))
      (Typed.liftClosed (Δ := ctorTele T fs) typed)
    rwa [subst_ids] at h
  refine ValidTmN.close laws (ctorTele T fs) (C := .const T) (f := .const k) validType partsType
    typed (fun args short => .inr (.inr ⟨k, args, fs.length, .inl roleK, short, rfl⟩))
    ⟨validResult, fun {m r ξ σ σ' Δ ς ς'} e {P} den => ?_⟩
  have fieldsN := EqSubstN.ctorFields laws fs.length le_rfl e
  rw [List.take_length] at fieldsN
  change DenN M ξ (.const T) P at den
  obtain ⟨field, rfl, hF⟩ := ValueSide.DenS.ind_inv laws.value den role
  have closed : ∀ {F : Tm Head 0}, Field.closed F ∈ fs → F ∈ closedFields cs :=
    fun hF' => mem_closedFields mem hF'
  have tL := e.typed typedApp
  have tR := typedApp.substitute (EqSubstN.substMor_right laws ctx.valid e)
  have conv : ∀ i, M.side.E.convTm Δ (ς i) (ς' i)
      (Presentation.subst ς (Ctx.lookup (ctorTele T fs) i)) := fun i => by
    obtain ⟨Q, -, -, h⟩ := e.lookup i
    exact (Q.real (σ i)).escape h
  have spine := convNe_telescope_apply M.side.laws (Θ := ctorTele T fs) (X := .const T) conv
    (M.side.laws.convNe_const k typedK)
  rw [subst_applyClosed_const, subst_applyClosed_const, subst_applyClosed_const,
    subst_applyClosed_const]
  rw [subst_applyClosed_const] at tL
  rw [subst_applyClosed_const] at tR
  rw [applyClosed_eq_appSpine, applyClosed_eq_appSpine] at spine
  change Typed M.side.R Δ _ (.const T) at tL tR
  change M.side.E.convNe Δ _ _ (.const T) at spine
  have convK : M.side.E.convTm Δ (appSpine (.const k) (telescopeArgs (ctorTele T fs) ς))
      (appSpine (.const k) (telescopeArgs (ctorTele T fs) ς')) (.const T) :=
    M.side.laws.convTm_of_convNe (.inr (.inl ⟨k, _, _, roleK, rfl⟩))
      (.inr (.inl ⟨k, _, _, roleK, rfl⟩)) spine
  refine ⟨.ctor mem .refl .refl (FieldsN.indFields den hF fieldsN closed), ?_⟩
  refine ⟨⟨tL, tR, convK⟩, fun ⟨s, hs⟩ => ?_⟩
  cases hs with
  | ctor mem' red shapes =>
      have e' := laws.value.unique red .refl (laws.value.ctorSpine_whnf role mem' _)
        (laws.value.ctorSpine_whnf role mem _)
      obtain ⟨rfl, rfl⟩ := appSpine_const_injective e'
      obtain rfl := laws.value.declared.fields_unique role mem mem'
      exact .inr ⟨cs, fs, _, _, realRole, mem,
        RedTy.refl (Typed.isType (S := M.side.toSetting) tL e.formed), .refl tL, .refl tR, convK,
        FieldsN.reals den hF fieldsN shapes closed⟩
  | star red daimonic =>
      exact (laws.value.ctorSpine_not_daimonic role mem .refl red daimonic).elim

/-! ## The recursor -/

/-- Methods over the motive `P`, one for each constructor, related at their case types, with
realizers related at their case types over the realizer motive `p`. -/
def MethodsN {n r : Nat} (ξ : World M.reading n) (Δ : Ctx Head r) (T : DeclName)
    (P : Tm Head n) (p : Tm Head r) (cs : List (DeclName × List (Field Head)))
    (ms ms' : List (Tm Head n)) (ms₀ ms₀' : List (Tm Head r)) : Prop :=
  ms.length = cs.length ∧ ms'.length = cs.length ∧ ms₀.length = cs.length ∧
    ms₀'.length = cs.length ∧
    ∀ {i : Nat} {k : DeclName} {fs : List (Field Head)}, cs[i]? = some (k, fs) →
      ∃ (g g' : Tm Head n) (g₀ g₀' : Tm Head r) (PM : NPack M n), ms[i]? = some g ∧
        ms'[i]? = some g' ∧ ms₀[i]? = some g₀ ∧ ms₀'[i]? = some g₀' ∧
        DenN M ξ (caseType T k fs P) PM ∧ PM.Related g g' Δ (caseType T k fs p) g₀ g₀'

namespace MethodsN

variable {n r : Nat} {ξ : World M.reading n} {Δ : Ctx Head r} {T : DeclName}
  {P : Tm Head n} {p : Tm Head r}

theorem nil : MethodsN ξ Δ T P p [] [] [] [] [] :=
  ⟨rfl, rfl, rfl, rfl, fun h => nomatch h⟩

theorem snoc {cs : List (DeclName × List (Field Head))} {ms ms' : List (Tm Head n)}
    {ms₀ ms₀' : List (Tm Head r)} (methods : MethodsN ξ Δ T P p cs ms ms' ms₀ ms₀')
    {k : DeclName} {fs : List (Field Head)} {g g' : Tm Head n} {g₀ g₀' : Tm Head r}
    {PM : NPack M n} (den : DenN M ξ (caseType T k fs P) PM)
    (rel : PM.Related g g' Δ (caseType T k fs p) g₀ g₀') :
    MethodsN ξ Δ T P p (cs ++ [(k, fs)]) (ms ++ [g]) (ms' ++ [g']) (ms₀ ++ [g₀])
      (ms₀' ++ [g₀']) := by
  obtain ⟨l, l', l₀, l₀', get⟩ := methods
  refine ⟨by simp [l], by simp [l'], by simp [l₀], by simp [l₀'], fun {i k' fs'} hi => ?_⟩
  rcases Nat.lt_or_ge i cs.length with lt | ge
  · rw [List.getElem?_append_left lt] at hi
    obtain ⟨h, h', h₀, h₀', PM', hh, hh', hh₀, hh₀', d, rel'⟩ := get hi
    exact ⟨h, h', h₀, h₀', PM', by rw [List.getElem?_append_left (l ▸ lt), hh],
      by rw [List.getElem?_append_left (l' ▸ lt), hh'],
      by rw [List.getElem?_append_left (l₀ ▸ lt), hh₀],
      by rw [List.getElem?_append_left (l₀' ▸ lt), hh₀'], d, rel'⟩
  · rw [List.getElem?_append_right ge] at hi
    obtain ⟨j, hj⟩ : ∃ j, i - cs.length = j := ⟨_, rfl⟩
    rw [hj] at hi
    cases j with
    | succ j => simp at hi
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        have ei : i = cs.length := by omega
        subst ei
        exact ⟨g, g', g₀, g₀', PM, by rw [List.getElem?_append_right (by omega)]; simp [l],
          by rw [List.getElem?_append_right (by omega)]; simp [l'],
          by rw [List.getElem?_append_right (by omega)]; simp [l₀],
          by rw [List.getElem?_append_right (by omega)]; simp [l₀'], den, rel⟩

/-- Related methods with related realizers are related methods. -/
theorem values {cs : List (DeclName × List (Field Head))} {ms ms' : List (Tm Head n)}
    {ms₀ ms₀' : List (Tm Head r)} (methods : MethodsN ξ Δ T P p cs ms ms' ms₀ ms₀') :
    MethodsV ξ T P cs ms ms' := by
  obtain ⟨l, l', -, -, get⟩ := methods
  refine ⟨l, l', fun hi => ?_⟩
  obtain ⟨g, g', _g₀, _g₀', PM, hg, hg', _hg₀, _hg₀', den, rel⟩ := get hi
  exact ⟨g, g', PM, hg, hg', den, rel.1⟩

/-- Methods related to others are related to themselves, with the same realizers. -/
theorem left (laws : M.Laws) {cs : List (DeclName × List (Field Head))}
    {ms ms' : List (Tm Head n)} {ms₀ ms₀' : List (Tm Head r)}
    (methods : MethodsN ξ Δ T P p cs ms ms' ms₀ ms₀') : MethodsN ξ Δ T P p cs ms ms ms₀ ms₀' := by
  obtain ⟨l, -, l₀, l₀', get⟩ := methods
  refine ⟨l, l, l₀, l₀', fun hi => ?_⟩
  obtain ⟨g, g', g₀, g₀', PM, hg, -, hg₀, hg₀', den, rel⟩ := get hi
  exact ⟨g, g, g₀, g₀', PM, hg, hg, hg₀, hg₀', den,
    ValueSide.DenS.refl_left laws.value den rel.1, rel.2⟩

end MethodsN

/-- **Related valuations of the recursor's prefix**: the motive at `T → v` and the methods at
their case types, related with related realizers. -/
theorem EqSubstN.recPrefix (laws : M.Laws) {T : DeclName} {v : Head}
    {cs : List (DeclName × List (Field Head))} :
    ∀ (j : Nat), j ≤ cs.length → ∀ {m r : Nat} {ξ : World M.reading m}
      {τ τ' : Sub Head (j + 1) m} {Δ : Ctx Head r} {ς ς' : Sub Head (j + 1) r},
      EqSubstN M (ofEntries (recEntry T v cs) (j + 1)) ξ τ τ' Δ ς ς' →
      (∃ RP : NPack M m, DenN M ξ (.pi (.const T) (.head v)) RP ∧
        RP.Related (τ (Fin.last j)) (τ' (Fin.last j)) Δ (.pi (.const T) (.head v))
          (ς (Fin.last j)) (ς' (Fin.last j))) ∧
      ∃ (ms ms' : List (Tm Head m)) (ms₀ ms₀' : List (Tm Head r)),
        telescopeArgs (ofEntries (recEntry T v cs) (j + 1)) τ = τ (Fin.last j) :: ms ∧
        telescopeArgs (ofEntries (recEntry T v cs) (j + 1)) τ' = τ' (Fin.last j) :: ms' ∧
        telescopeArgs (ofEntries (recEntry T v cs) (j + 1)) ς = ς (Fin.last j) :: ms₀ ∧
        telescopeArgs (ofEntries (recEntry T v cs) (j + 1)) ς' = ς' (Fin.last j) :: ms₀' ∧
        MethodsN ξ Δ T (τ (Fin.last j)) (ς (Fin.last j)) (cs.take j) ms ms' ms₀ ms₀'
  | 0, _, _, _, ξ, τ, τ', Δ, ς, ς', e => by
      obtain ⟨-, RP, den, rel⟩ := e
      exact ⟨⟨RP, den, rel⟩, [], [], [], [], rfl, rfl, rfl, rfl, MethodsN.nil⟩
  | j + 1, hj, _, _, ξ, τ, τ', Δ, ς, ς', e => by
      obtain ⟨tail, PM, denM, rel⟩ := e
      obtain ⟨motive, ms, ms', ms₀, ms₀', hms, hms', hms₀, hms₀', methods⟩ :=
        EqSubstN.recPrefix laws j (by omega) tail
      have hget : cs[j]? = some cs[j] := List.getElem?_eq_getElem (by omega)
      rcases hc : cs[j] with ⟨k, fs⟩
      rw [hc] at hget
      rw [recEntry_method T v cs hget, subst_caseType] at denM rel
      refine ⟨motive, ms ++ [τ 0], ms' ++ [τ' 0], ms₀ ++ [ς 0], ms₀' ++ [ς' 0], ?_, ?_, ?_, ?_,
        ?_⟩
      · rw [telescopeArgs_ofEntries_succ, hms]
        rfl
      · rw [telescopeArgs_ofEntries_succ, hms']
        rfl
      · rw [telescopeArgs_ofEntries_succ, hms₀]
        rfl
      · rw [telescopeArgs_ofEntries_succ, hms₀']
        rfl
      · rw [List.take_succ_eq_append_getElem (by omega), hc]
        exact methods.snoc denM rel

/-- The motive at two equal terms of the inductive type gives equal types, on the realizer
side. -/
theorem motive_typeEq {v : Head} (realHv : M.side.R.isUniverse v) {T : DeclName} {r : Nat}
    {Δ : Ctx Head r} {p p' : Tm Head r}
    (equalP : Equal M.side.R Δ p p' (.pi (.const T) (.head v))) {b b' : Tm Head r}
    (equal : Equal M.side.R Δ b b' (.const T)) :
    TypeEq M.side.R Δ (.app p b) (.app p' b') :=
  ⟨_, realHv, .appCong (B := .head v) equalP equal⟩

/-- Fields related with realizers number the fields, on the realizer side. -/
theorem FieldsN.length {n r : Nat} {ξ : World M.reading n} {Δ : Ctx Head r} {T : DeclName} :
    ∀ {fs : List (Field Head)} {as as' : List (Tm Head n)} {us us' : List (Tm Head r)},
      FieldsN ξ Δ T fs as as' us us' → us.length = fs.length ∧ us'.length = fs.length
  | _, _, _, _, _, .nil => ⟨rfl, rfl⟩
  | _, _, _, _, _, .cons _ rest => by
      obtain ⟨h, h'⟩ := FieldsN.length rest
      exact ⟨by simp [h], by simp [h']⟩

section Realizers

variable (laws : M.Laws) {T rec : DeclName} {cs : List (DeclName × List (Field Head))}
  (decl : InductiveValues M.value T rec cs) {v : Head}
  (realDecl : DeclaresRecursor M.side.toSetting T cs rec v)
  (realRole : M.side.roles T = .inductive cs)
  (realIota : ∀ {n : Nat} {l r : Tm Head n}, IotaStep rec cs l r → M.side.R.computation.step l r)
  (realHv : M.side.R.isUniverse v)
  {n r : Nat} {ξ : World M.reading n} {Δ : Ctx Head r} (formed : CtxFormed M.side.R Δ)
  {τ τ' : Sub Head (cs.length + 1) r}
  (typedτ : SubstMor M.side.R (recPrefix T v cs) Δ τ)
  (typedτ' : SubstMor M.side.R (recPrefix T v cs) Δ τ')
  (convτ : ∀ i, M.side.E.convTm Δ (τ i) (τ' i)
    (Presentation.subst τ (Ctx.lookup (recPrefix T v cs) i)))
  (equalP : Equal M.side.R Δ (τ (Fin.last cs.length)) (τ' (Fin.last cs.length))
    (.pi (.const T) (.head v)))

include realDecl realHv formed typedτ typedτ' convτ equalP in
/-- **The recursor's realizers at realizers reaching neutral terms**: both applications reach
neutral spines, which the generic equality compares argument by argument, so they are related
by every candidate at the realizer motive at the first scrutinee. -/
theorem rec_neutral {t t' : Tm Head r} (ne : NeRel M.side Δ (.const T) t t')
    (X : ECand M.side) :
    X.rel Δ (.app (τ (Fin.last cs.length)) t) (.app (recHead rec T v cs τ) t)
      (.app (recHead rec T v cs τ') t') := by
  have ett' : Equal M.side.R Δ t t' (.const T) := M.side.laws.convTm_sound (NeRel.escape ne)
  obtain ⟨w, w', r₀, r₀', nw, nw', cv⟩ := ne
  have tp := (methods_of_substMor (R := M.side.R) cs.length le_rfl typedτ).1
  have typeT : IsType M.side.R Δ (.app (τ (Fin.last cs.length)) t) :=
    Typed.isType (S := M.side.toSetting) (realDecl.app_typing typedτ r₀.source) formed
  have here : TypeEq M.side.R Δ (.app (τ (Fin.last cs.length)) w)
      (.app (τ (Fin.last cs.length)) t) :=
    motive_typeEq realHv (.refl tp) (.symm r₀.equal)
  have there : TypeEq M.side.R Δ (.app (τ' (Fin.last cs.length)) t')
      (.app (τ (Fin.last cs.length)) t) :=
    motive_typeEq realHv (.symm equalP) (.symm ett')
  have thereW : TypeEq M.side.R Δ (.app (τ' (Fin.last cs.length)) w')
      (.app (τ (Fin.last cs.length)) t) :=
    motive_typeEq realHv (.symm equalP) (.trans (.symm r₀'.equal) (.symm ett'))
  have redN := realDecl.scrutinee_red typedτ r₀ (IsType.refl typeT) here
  have redN' := realDecl.scrutinee_red typedτ' r₀' there thereW
  have role : ∀ {τ₀ : Sub Head (cs.length + 1) r}, M.side.roles rec = .computes (cs.length + 2)
      (.split (telescopeArgs (recPrefix T v cs) τ₀).length .constructor fun _ => .leaf) := by
    intro τ₀
    rw [telescopeArgs_length]
    exact realDecl.recRole
  have lengthOk : ∀ {τ₀ : Sub Head (cs.length + 1) r},
      (telescopeArgs (recPrefix T v cs) τ₀).length + 1 + ([] : List (Tm Head r)).length =
        cs.length + 2 := by
    intro τ₀
    rw [telescopeArgs_length]
    rfl
  have hN : Neutral M.side.roles (.app (recHead rec T v cs τ) w) := by
    rw [app_recHead, recApp]
    exact .stuck_single (after := []) role lengthOk nw
  have hN' : Neutral M.side.roles (.app (recHead rec T v cs τ') w') := by
    rw [app_recHead, recApp]
    exact .stuck_single (after := []) role lengthOk nw'
  have spine := M.side.laws.convNe_app (realDecl.head_convNe M.side.laws convτ)
    (M.side.laws.convTm_of_convNe (.inl nw) (.inl nw') cv)
  rw [inst0_motiveApp] at spine
  exact X.expand redN redN' (X.neutral hN hN' redN.target redN'.target
    (M.side.laws.convNe_conv spine here))

include laws decl realDecl realRole realIota realHv formed typedτ typedτ' convτ equalP in
/-- **The realizers of the recursor**, by induction on the derivation of the shape of the
scrutinee's value: realizers of a constructor shape reach that constructor, with fields related
by the candidates of the shapes of the fields, so both recursor applications reach the method's
realizers applied to the fields and to the recursive calls, related by the realizers of the
method's value; realizers of the daimon's shape reach neutral terms, where both applications
are stuck. -/
theorem rec_claim {field : Tm Head 0 → NPack M n}
    (hT : DenN M ξ (.const T) (indPack M.value T cs field))
    (hF : ∀ {F : Tm Head 0}, F ∈ closedFields cs → DenN M ξ (liftClosed F) (field F))
    (hv : M.rules.isUniverse v) {RP : NPack M n}
    (denP : DenN M ξ (.pi (.const T) (.head v)) RP) {P : Tm Head n} (relP : RP.rel P P)
    {ms : List (Tm Head n)} {ms₀ ms₀' : List (Tm Head r)}
    (hms₀ : telescopeArgs (recPrefix T v cs) τ = τ (Fin.last cs.length) :: ms₀)
    (hms₀' : telescopeArgs (recPrefix T v cs) τ' = τ' (Fin.last cs.length) :: ms₀')
    (methods : MethodsN ξ Δ T P (τ (Fin.last cs.length)) cs ms ms ms₀ ms₀') :
    ∀ {t₀ : Tm Head n} {s : IndShape Head n}, HasIndShape M.value cs t₀ s →
      IndRel M.value cs field t₀ t₀ → ∀ {t t' : Tm Head r},
      (s.real M.value T field).rel Δ (.const T) t t' →
      ∀ {Q : NPack M n}, DenN M ξ (.app P t₀) Q →
        (Q.real (recApp rec (P :: ms) t₀)).rel Δ (.app (τ (Fin.last cs.length)) t)
          (.app (recHead rec T v cs τ) t) (.app (recHead rec T v cs τ') t') := by
  have tp := (methods_of_substMor (R := M.side.R) cs.length le_rfl typedτ).1
  have headsRA : recApp rec (τ (Fin.last cs.length) :: ms₀) =
      Tm.app (recHead rec T v cs τ) := by
    funext x
    rw [app_recHead, hms₀]
  have headsRA' : recApp rec (τ' (Fin.last cs.length) :: ms₀') =
      Tm.app (recHead rec T v cs τ') := by
    funext x
    rw [app_recHead, hms₀']
  intro t₀ s h
  refine HasIndShape.rec
    (motive_1 := fun t₀ s _ => IndRel M.value cs field t₀ t₀ → ∀ {t t' : Tm Head r},
      (s.real M.value T field).rel Δ (.const T) t t' → ∀ {Q : NPack M n},
        DenN M ξ (.app P t₀) Q →
        (Q.real (recApp rec (P :: ms) t₀)).rel Δ (.app (τ (Fin.last cs.length)) t)
          (.app (recHead rec T v cs τ) t) (.app (recHead rec T v cs τ') t'))
    (motive_2 := fun fs as fields _ => IndFields M.value cs field fs as as →
      (∀ {F : Tm Head 0}, Field.closed F ∈ fs → F ∈ closedFields cs) →
      ∀ {us us' : List (Tm Head r)},
        FieldsRel T Δ (IndShapes.reals M.value T field fields) fs us us' →
        FieldsN ξ Δ T fs as as us us' ∧
        HypsN ξ Δ P (τ (Fin.last cs.length)) (recArgs fs as) (recArgs fs us)
          ((recArgs fs as).map (recApp rec (P :: ms)))
          ((recArgs fs as).map (recApp rec (P :: ms)))
          ((recArgs fs us).map (.app (recHead rec T v cs τ)))
          ((recArgs fs us').map (.app (recHead rec T v cs τ'))))
    ?_ ?_ ?_ ?_ ?_ h
  · intro k fs t₀ as fields mem red₀ shapes₀ ih valid t t' ht Q den
    change (ECand.ctorReal M.side T k (IndShapes.reals M.value T field fields)).rel Δ
      (.const T) t t' at ht
    rcases ht with ne | ⟨cs', fs', us, us', role', mem', -, r₀, r₀', cv, fieldsRel⟩
    · exact rec_neutral realDecl realHv formed typedτ typedτ' convτ equalP ne _
    obtain rfl := Role.inductive.inj (realRole.symm.trans role')
    obtain rfl := M.side.constructors.fields_unique realRole mem mem'
    have valFields := ValueSide.IndRel.val_fields decl laws.value valid mem red₀
    obtain ⟨fieldsN, hyps⟩ := ih valFields (fun hF' => mem_closedFields mem hF') fieldsRel
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp mem
    obtain ⟨g, g', g₀, g₀', PM, hg, hg', hg₀, hg₀', denM, relM⟩ := methods.2.2.2.2 hi
    obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
    obtain ⟨R', denR', relR'⟩ := method_app laws formed fieldsN hyps denM relM
    have toCtor : IndRel M.value cs field t₀ (appSpine (.const k) as) :=
      .ctor mem red₀ .refl valFields
    obtain ⟨R₀, den₀, denCtor⟩ := ValueSide.motive_den laws.value hT hv denP relP toCtor
    have eQ : Q = R' := (ValueSide.DenS.deterministic laws.value den den₀).trans
      (ValueSide.DenS.deterministic laws.value denCtor denR')
    subst eQ
    have relRec : Q.rel (recApp rec (P :: ms) t₀)
        (appSpine g (as ++ (recArgs fs as).map (recApp rec (P :: ms)))) :=
      (ValueSide.DenS.expansive laws.value den).left
        (ValueSide.rec_red_ctor decl methods.1 hi hg (ValueSide.IndFields.length valFields).1
          red₀) relR'.1
    rw [ValueSide.DenS.real_eq_of_rel laws.value den relRec]
    have ett' : Equal M.side.R Δ t t' (.const T) := M.side.laws.convTm_sound cv
    have typeT : IsType M.side.R Δ (.app (τ (Fin.last cs.length)) t) :=
      Typed.isType (S := M.side.toSetting) (realDecl.app_typing typedτ r₀.source) formed
    have toK : TypeEq M.side.R Δ (.app (τ (Fin.last cs.length)) (appSpine (.const k) us))
        (.app (τ (Fin.last cs.length)) t) :=
      motive_typeEq realHv (.refl tp) (.symm r₀.equal)
    have there : TypeEq M.side.R Δ (.app (τ' (Fin.last cs.length)) t')
        (.app (τ (Fin.last cs.length)) t) :=
      motive_typeEq realHv (.symm equalP) (.symm ett')
    have thereK : TypeEq M.side.R Δ (.app (τ' (Fin.last cs.length)) (appSpine (.const k) us'))
        (.app (τ (Fin.last cs.length)) t) :=
      motive_typeEq realHv (.symm equalP) (.trans (.symm r₀'.equal) (.symm ett'))
    obtain ⟨lenUs, lenUs'⟩ := FieldsN.length fieldsN
    have step := realIota ⟨τ (Fin.last cs.length), ms₀, i, k, fs, us, g₀, methods.2.2.1, hi,
      lenUs, hg₀, rfl, rfl⟩
    have step' := realIota ⟨τ' (Fin.last cs.length), ms₀', i, k, fs, us', g₀', methods.2.2.2.1,
      hi, lenUs', hg₀', rfl, rfl⟩
    rw [headsRA] at step
    rw [headsRA'] at step'
    obtain ⟨tL, tR⟩ := (Q.real _).typed relR'.2
    have red := (realDecl.scrutinee_red typedτ r₀ (IsType.refl typeT) toK).trans
      (RedTm.root step (Typed.convType (realDecl.app_typing typedτ r₀.target) toK)
        (Typed.convType tL toK))
    have red' := (realDecl.scrutinee_red typedτ' r₀' there thereK).trans
      (RedTm.root step' (Typed.convType (realDecl.app_typing typedτ' r₀'.target) thereK)
        (Typed.convType tR toK))
    exact (Q.real _).expand red red' ((Q.real _).conv formed toK relR'.2)
  · intro t₀ u red daimonic valid t t' ht Q den
    exact rec_neutral realDecl realHv formed typedτ typedτ' convτ equalP ht _
  · intro _ _ us us' rel
    cases rel
    exact ⟨.nil, .nil⟩
  · intro fs a as shape rest hshape _ ihHead ihRest fieldsRel closed us us' rel
    change FieldsRel T Δ (shape.real M.value T field :: IndShapes.reals M.value T field rest)
      (.recursive :: fs) us us' at rel
    rcases rel with _ | ⟨hx, restRel'⟩
    cases fieldsRel with
    | recursive headRel restRel =>
        obtain ⟨fieldsN, hyps⟩ := ihRest restRel (fun hF' => closed (List.mem_cons_of_mem _ hF'))
          restRel'
        refine ⟨.cons (fun d => ?_) fieldsN, .cons (fun d => ⟨ValueSide.rec_related decl
          laws.value hT hF hv denP relP methods.values headRel d, ihHead headRel hx d⟩) hyps⟩
        rw [ValueSide.DenS.deterministic laws.value d hT]
        refine ⟨headRel, ?_⟩
        rw [ValueSide.indPack_real_of_shape laws.value decl.role hshape]
        exact hx
  · intro F fs a as rest _ ihRest fieldsRel closed us us' rel
    change FieldsRel T Δ ((field F).real a :: IndShapes.reals M.value T field rest)
      (.closed F :: fs) us us' at rel
    rcases rel with _ | ⟨hx, restRel'⟩
    cases fieldsRel with
    | closed hRel restRel =>
        obtain ⟨fieldsN, hyps⟩ := ihRest restRel (fun hF' => closed (List.mem_cons_of_mem _ hF'))
          restRel'
        refine ⟨.cons (fun d => ?_) fieldsN, hyps⟩
        rw [ValueSide.DenS.deterministic laws.value d (hF (closed List.mem_cons_self))]
        exact ⟨hRel, hx⟩

end Realizers

/-! ## Validity of the recursor -/

/-- **The recursor is a valid term of its declared type**, with its motive into the universe
`v`: its values at related arguments are related by induction on the inductive pack
(`ValueSide.rec_related`), and its realizer instances are related by the realizers of its value
at the scrutinee's value, by recursion on the shape of that value (`rec_claim`). The validity
of the declared type and of its parts are hypotheses, which the fundamental lemma of a smaller
stage provides. -/
theorem ValidTmN.inductiveRec (laws : M.Laws) {T rec : DeclName}
    {cs : List (DeclName × List (Field Head))} (decl : InductiveValues M.value T rec cs)
    {v : Head} (realDecl : DeclaresRecursor M.side.toSetting T cs rec v)
    (realRole : M.side.roles T = .inductive cs)
    (realIota : ∀ {n : Nat} {l r : Tm Head n}, IotaStep rec cs l r →
      M.side.R.computation.step l r)
    (hv : M.rules.isUniverse v) (realHv : M.side.R.isUniverse v)
    (validType : ValidTyN M .nil (recType T v cs))
    (partsType : StructuredN M .nil (recType T v cs)) :
    ValidTmN M .nil (.const rec) (recType T v cs) := by
  obtain ⟨ctx, validResult, _⟩ :=
    ValidTyN.close_parts (recTele T v cs) (C := recBody cs.length) validType partsType
  have typed : Typed M.side.R .nil (.const rec) (recType T v cs) := by
    have h := realDecl.rec_typing (Γ := .nil)
    rwa [liftClosed_zero] at h
  refine ValidTmN.close laws (recTele T v cs) (C := recBody cs.length) (f := .const rec)
    validType partsType typed
    (fun args short => .inr (.inr ⟨rec, args, cs.length + 2, .inr ⟨_, realDecl.recRole⟩, short,
      rfl⟩))
    ⟨validResult, fun {m r ξ σ σ' Δ ς ς'} e {R} den => ?_⟩
  have formed := e.formed
  rw [subst_applyClosed_const, subst_applyClosed_const, subst_applyClosed_const,
    subst_applyClosed_const]
  obtain ⟨prefixE, PT, denT, relT⟩ := e
  rw [recEntry_scrutinee] at denT relT
  change DenN M ξ (.const T) PT at denT
  change PT.Related (σ 0) (σ' 0) Δ (.const T) (ς 0) (ς' 0) at relT
  obtain ⟨field, rfl, hF⟩ := ValueSide.DenS.ind_inv laws.value denT decl.role
  obtain ⟨⟨RP, denP, relP, realP⟩, ms, ms', ms₀, ms₀', hms, hms', hms₀, hms₀', methods⟩ :=
    EqSubstN.recPrefix laws cs.length le_rfl prefixE
  rw [List.take_length] at methods
  have args : ∀ {k : Nat} (τ : Sub Head (cs.length + 2) k),
      telescopeArgs (recTele T v cs) τ =
        telescopeArgs (ofEntries (recEntry T v cs) (cs.length + 1)) (tailSub τ) ++ [τ 0] :=
    fun _ => rfl
  have typedτ : SubstMor M.side.R (recPrefix T v cs) Δ (tailSub ς) := prefixE.substMor
  have typedτ' : SubstMor M.side.R (recPrefix T v cs) Δ (tailSub ς') :=
    EqSubstN.substMor_right laws ctx.1.valid prefixE
  have convτ : ∀ i, M.side.E.convTm Δ (tailSub ς i) (tailSub ς' i)
      (Presentation.subst (tailSub ς) (Ctx.lookup (recPrefix T v cs) i)) := fun i => by
    obtain ⟨Q, -, -, h⟩ := prefixE.lookup i
    exact (Q.real _).escape h
  have appL : appSpine (.const rec) (telescopeArgs (recTele T v cs) ς) =
      .app (recHead rec T v cs (tailSub ς)) (ς 0) := by
    rw [args, app_recHead]
    rfl
  have appR : appSpine (.const rec) (telescopeArgs (recTele T v cs) ς') =
      .app (recHead rec T v cs (tailSub ς')) (ς' 0) := by
    rw [args, app_recHead]
    rfl
  rw [appL, appR, args σ, args σ', hms, hms']
  change DenN M ξ (.app (σ (Fin.last (cs.length + 1))) (σ 0)) R at den
  refine ⟨ValueSide.rec_related decl laws.value denT hF hv denP relP methods.values relT.1 den, ?_⟩
  obtain ⟨s, hs⟩ := ValueSide.IndRel.hasShape relT.1
  have valid := ValueSide.DenS.refl_left laws.value denT relT.1
  have ha : (s.real M.value T field).rel Δ (.const T) (ς 0) (ς' 0) := by
    rw [← ValueSide.indPack_real_of_shape laws.value decl.role hs]
    exact relT.2
  exact rec_claim laws decl realDecl realRole realIota realHv formed typedτ typedτ' convτ
    ((RP.real _).equal realP) denT hF hv denP (ValueSide.DenS.refl_left laws.value denP relP)
    hms₀ hms₀' (methods.left laws) hs valid ha den

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
