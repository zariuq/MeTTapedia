import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.Fundamental
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.CodeConstants
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.IotaComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Spines
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Motives

/-!
# A simple inductive type in model SN

A simple inductive type `T` lists its constructors, each with fields that are `T` itself or a
closed type, and its recursor `rec` computes by one rule per constructor,
`rec P m₁ ⋯ m_c (kᵢ a₁ ⋯ aₐ) ⟶ mᵢ a₁ ⋯ aₐ (rec P m₁ ⋯ m_c aⱼ) ⋯`, with a recursive call at each
recursive field. This module gives its three clauses in model SN, for every such type at once:

* **the type** (`ValidTmS.inductiveType`): at every world `T` denotes its inductive pack, over
  the packs of its closed field types. The pack relates two terms when they reduce to one
  constructor with related fields, recursive fields by the pack itself, or both to terms stuck on
  the daimon: it is the least relation closed under the constructors, an inductive definition.
  A value is realized by the meet of the realizers of its shapes: a constructor candidate of the
  realizers of its fields, or the terms that reach no constructor;
* **the constructors** (`ValidTmS.inductiveCtor`): a constructor applied to related fields is
  related to itself applied to the other fields, and applied to realizers of the fields it
  realizes every shape of the value;
* **the recursor** (`ValidTmS.inductiveRec`), with its motive into any universe: by induction on
  the inductive pack. At a constructor both sides compute to the method applied to the fields
  and to the recursive calls, related by induction, and a method applied to related fields and
  hypotheses gives related results, one binder at a time (`method_app`). At terms stuck on the
  daimon both sides are stuck. The realizers are proved by induction on the derivation of a shape
  of a value: the recursor applied to realizers lies in the meet, over the values of that shape,
  of the realizers of the recursor's values (`recFamily`). A realizer of a constructor shape
  reaches only that constructor, with fields realizing the shapes of the fields; one that reaches
  no constructor never computes.

The induction on the pack is what the clause needs: a relation that also related terms reaching
no constructor, other than the daimon, would leave the recursor stuck at them with no method to
read.

**What the type asks of the model** (`InductiveIn`): `T` is an inductive type with the
constructors `cs` on both sides, each constructor a constructor of its number of fields on the
realizer side, the recursor computes by the rules of `cs` on the value side, and on the realizer
side its root steps are exactly those rules.

Positive examples: the numbers, with `zero` without fields and `suc` with one recursive field,
are an instance, and the transport value model's `zero`, `suc` and `num-rec` are these clauses
(`ExecutableModel.CodeModel.TExtension.valid_zero`, `valid_suc`, `valid_numRec`); the lists of
numbers, with `nil` and `cons` of a number and a list, are another, as is every simple datatype
admissible over the object package (`ExecutableModel.CodeModel.dataTExt_valid_rec`). Negative
example: the clauses fix the realizer side's root steps at the recursor to the rules of `cs`
(`InductiveIn.realIota`); a recursor whose rule at `cons` recurses on the same list meets no such
requirement, and its package is not strongly normalizing
(`ExecutableModel.CodeModel.loopRules_not_sn`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ModelSN

open Normalization hiding World Pack
open UniverseLevel (LevelOrder)
open Consistency (World Morph)
open Realizability (Daimonic)
open StrongNormalization
open TelescopeAbstraction (closeType applyClosed applyClosed_subst liftClosed_zero)
open ValueSide

variable {Head L : Type} [LevelOrder L] {M : SNModel Head L}

/-! ## The type in the model -/

/-- **A simple inductive type read in model SN**: `T` is an inductive type with the
constructors `cs` on both sides, whose constructors are constructors on the realizer side, and
the recursor `rec` computes by the rules of `cs` on the value side; on the realizer side its
root steps are those rules. -/
structure InductiveIn (M : SNModel Head L) (T rec : DeclName)
    (cs : List (DeclName × List (Field Head))) : Prop where
  role : M.roles T = .inductive cs
  recRole : M.roles rec =
    .computes (cs.length + 2) (.split (cs.length + 1) .constructor fun _ => .leaf)
  iota : ∀ {n : Nat} {l r : Tm Head n}, IotaStep rec cs l r → M.rules.computation.step l r
  realRole : M.realizers.roles T = .inductive cs
  realDeclared : ConstructorsDeclared M.realizers.roles
  realRecRole : M.realizers.roles rec =
    .computes (cs.length + 2) (.split (cs.length + 1) .constructor fun _ => .leaf)
  realIota : ∀ {n : Nat} {args : List (Tm Head n)} {r : Tm Head n},
    M.realizers.rules.computation.step (appSpine (.const rec) args) r →
      IotaStep rec cs (appSpine (.const rec) args) r

/-- The value side of a simple inductive type read in model SN. -/
theorem InductiveIn.values {T rec : DeclName} {cs : List (DeclName × List (Field Head))}
    (decl : InductiveIn M T rec cs) : InductiveValues M.value T rec cs :=
  ⟨decl.role, decl.recRole, decl.iota⟩

/-! ## Related values with a realizer -/

/-- A pack relates two values and the first has a realizer. -/
def Rel3 {n r : Nat} (P : Pack M.value n) (a a' : Tm Head n) (u : Tm Head r) : Prop :=
  P.rel a a' ∧ (P.real a).mem u

section Application

variable (laws : M.Laws)
include laws

/-- Related functions with a realizer, applied to related arguments with a realizer, give
related results with a realizer at a denotation of the codomain. -/
theorem DenS.pi_app_rel3 {n r : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : Pack M.value n} (den : DenS M.value ξ (.pi A B) P)
    {f f' a a' : Tm Head n} {t u : Tm Head r} (hf : Rel3 P f f' t)
    (ha : ∀ {PA : Pack M.value n}, DenS M.value ξ A PA → Rel3 PA a a' u) :
    ∃ PB, DenS M.value ξ (inst0 a B) PB ∧ Rel3 PB (.app f a) (.app f' a') (.app t u) := by
  obtain ⟨PB, denB, rel⟩ := DenS.pi_app_exists laws den hf.1 fun d => (ha d).1
  exact ⟨PB, denB, rel, DenS.pi_app_real laws den hf.2
    (fun d => DenS.refl_left laws.value d (ha d).1) (fun d => (ha d).2) denB⟩

end Application

/-- The fields of a constructor, related at the denotations of their types, each with a
realizer. -/
inductive FieldsS {n : Nat} (ξ : World M.reading n) (T : DeclName) {r : Nat} :
    List (Field Head) → List (Tm Head n) → List (Tm Head n) → List (Tm Head r) → Prop where
  | nil : FieldsS ξ T [] [] [] []
  | cons {f : Field Head} {a a' : Tm Head n} {u : Tm Head r} {fs : List (Field Head)}
      {as as' : List (Tm Head n)} {us : List (Tm Head r)} :
      (∀ {PA : Pack M.value n}, DenS M.value ξ (liftClosed (f.type T)) PA → Rel3 PA a a' u) →
      FieldsS ξ T fs as as' us → FieldsS ξ T (f :: fs) (a :: as) (a' :: as') (u :: us)

/-- Induction hypotheses over the motive `p`, related at the motive at their fields, each with
a realizer. -/
inductive HypsS {n : Nat} (ξ : World M.reading n) (p : Tm Head n) {r : Nat} :
    List (Tm Head n) → List (Tm Head n) → List (Tm Head n) → List (Tm Head r) → Prop where
  | nil : HypsS ξ p [] [] [] []
  | cons {x ih ih' : Tm Head n} {ih₀ : Tm Head r} {xs ihs ihs' : List (Tm Head n)}
      {ihs₀ : List (Tm Head r)} :
      (∀ {R : Pack M.value n}, DenS M.value ξ (.app p x) R → Rel3 R ih ih' ih₀) →
      HypsS ξ p xs ihs ihs' ihs₀ → HypsS ξ p (x :: xs) (ih :: ihs) (ih' :: ihs') (ih₀ :: ihs₀)

section Application

variable (laws : M.Laws)
include laws

/-- A function of the induction hypotheses, applied to related hypotheses with realizers. -/
theorem caseHyps_app {n r : Nat} {ξ : World M.reading n} {p target : Tm Head n} :
    ∀ {xs ihs ihs' : List (Tm Head n)} {ihs₀ : List (Tm Head r)}, HypsS ξ p xs ihs ihs' ihs₀ →
      ∀ {g g' : Tm Head n} {g₀ : Tm Head r} {PM : Pack M.value n},
        DenS M.value ξ (caseHyps p xs target) PM → Rel3 PM g g' g₀ →
        ∃ R, DenS M.value ξ (.app p target) R ∧
          Rel3 R (appSpine g ihs) (appSpine g' ihs') (appSpine g₀ ihs₀)
  | _, _, _, _, .nil, g, g', g₀, PM, den, h => by
      rw [caseHyps_nil] at den
      exact ⟨PM, den, h⟩
  | _, _, _, _, .cons (x := x) hx tail, g, g', g₀, PM, den, h => by
      rw [caseHyps_cons] at den
      obtain ⟨PB, denB, hB⟩ := DenS.pi_app_rel3 laws den h hx
      rw [inst0_caseHyps] at denB
      exact caseHyps_app tail denB hB

/-- A method applied to related fields with realizers, through the fields of its case type. -/
theorem caseFields_app {n r : Nat} {ξ : World M.reading n} {T k : DeclName} :
    ∀ {fs : List (Field Head)} {as as' : List (Tm Head n)} {us : List (Tm Head r)},
      FieldsS ξ T fs as as' us →
      ∀ {p : Tm Head n} {xs recs : List (Tm Head n)} {g g' : Tm Head n} {g₀ : Tm Head r}
        {PM : Pack M.value n}, DenS M.value ξ (caseFields T k fs p xs recs) PM →
        Rel3 PM g g' g₀ →
        ∃ PH, DenS M.value ξ (caseHyps p (recs ++ recArgs fs as) (appSpine (.const k) (xs ++ as)))
          PH ∧ Rel3 PH (appSpine g as) (appSpine g' as') (appSpine g₀ us)
  | _, _, _, _, .nil, p, xs, recs, g, g', g₀, PM, den, h => by
      simp only [caseFields, recArgs, List.append_nil] at den ⊢
      exact ⟨PM, den, h⟩
  | .recursive :: fs, a :: as, _, _, .cons ha tail, p, xs, recs, g, g', g₀, PM, den, h => by
      simp only [caseFields] at den
      obtain ⟨PB, denB, hB⟩ := DenS.pi_app_rel3 laws den h ha
      rw [inst0_caseFields T k fs a p xs recs [.var 0] [a] rfl] at denB
      obtain ⟨PH, denH, hH⟩ := caseFields_app tail denB hB
      simp only [List.append_assoc, List.singleton_append] at denH
      exact ⟨PH, denH, hH⟩
  | .closed F :: fs, a :: as, _, _, .cons ha tail, p, xs, recs, g, g', g₀, PM, den, h => by
      simp only [caseFields] at den
      obtain ⟨PB, denB, hB⟩ := DenS.pi_app_rel3 laws den h ha
      have inst := inst0_caseFields T k fs a p xs recs [] [] rfl
      rw [List.append_nil, List.append_nil] at inst
      rw [inst] at denB
      obtain ⟨PH, denH, hH⟩ := caseFields_app tail denB hB
      simp only [List.append_assoc, List.singleton_append] at denH
      exact ⟨PH, denH, hH⟩

/-- **A method applied to related fields and hypotheses** gives related results with a
realizer, at the motive at the constructor applied to the fields. -/
theorem method_app {n r : Nat} {ξ : World M.reading n} {T k : DeclName} {fs : List (Field Head)}
    {as as' : List (Tm Head n)} {us : List (Tm Head r)} (fields : FieldsS ξ T fs as as' us)
    {p : Tm Head n} {ihs ihs' : List (Tm Head n)} {ihs₀ : List (Tm Head r)}
    (hyps : HypsS ξ p (recArgs fs as) ihs ihs' ihs₀) {g g' : Tm Head n} {g₀ : Tm Head r}
    {PM : Pack M.value n} (den : DenS M.value ξ (caseType T k fs p) PM) (hg : Rel3 PM g g' g₀) :
    ∃ R, DenS M.value ξ (.app p (appSpine (.const k) as)) R ∧
      Rel3 R (appSpine g (as ++ ihs)) (appSpine g' (as' ++ ihs')) (appSpine g₀ (us ++ ihs₀)) := by
  obtain ⟨PH, denH, hH⟩ := caseFields_app laws fields den hg
  simp only [List.nil_append] at denH
  obtain ⟨R, denR, hR⟩ := caseHyps_app laws hyps denH hH
  refine ⟨R, denR, ?_⟩
  rw [appSpine_append, appSpine_append, appSpine_append]
  exact hR

end Application


/-! ## Constructor spines on the realizer side -/

/-- A step of one listed term keeps a list of reducts a list of reducts. -/
theorem forall₂_reducesStar_step {R : Rules Head} {n : Nat} {a a' : Tm Head n}
    (s : StrongNormalization.Reduces R a a') :
    ∀ (pre : List (Tm Head n)) {post us : List (Tm Head n)},
      List.Forall₂ (StrongNormalization.ReducesStar R) us (pre ++ a :: post) →
        List.Forall₂ (StrongNormalization.ReducesStar R) us (pre ++ a' :: post)
  | [], _, _, .cons h rest => .cons (h.tail s) rest
  | _ :: pre, _, _, .cons h rest => .cons h (forall₂_reducesStar_step s pre rest)

/-- Members of candidates stay members along reductions. -/
theorem forall₂_mem_reducts {r : Nat} :
    ∀ {Xs : List M.Cand} {us us' : List (Tm Head r)},
      List.Forall₂ (fun (X : M.Cand) (u : Tm Head r) => X.mem u) Xs us →
      List.Forall₂ (ReducesStar M.realizers.rules) us us' →
      List.Forall₂ (fun (X : M.Cand) (u : Tm Head r) => X.mem u) Xs us'
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h hs, .cons s ss => .cons (KCand.reducts _ h s) (forall₂_mem_reducts hs ss)

/-- Members of candidates are strongly normalizing. -/
theorem forall₂_mem_sn {r : Nat} :
    ∀ {Xs : List M.Cand} {us : List (Tm Head r)},
      List.Forall₂ (fun (X : M.Cand) (u : Tm Head r) => X.mem u) Xs us →
      ∀ u ∈ us, SN M.realizers.rules u
  | _, _, .nil => fun _ h => nomatch h
  | _, _, .cons h hs => fun u hu => by
      rcases List.mem_cons.mp hu with rfl | hu
      · exact KCand.sn _ h
      · exact forall₂_mem_sn hs u hu

/-- A spine of a constant that never computes on the realizer side reduces only in its
arguments. -/
theorem reducesStar_constSpine {c : DeclName}
    (stuck : ∀ arity inspect, M.realizers.roles c ≠ .computes arity inspect) {r : Nat}
    {us : List (Tm Head r)} {w : Tm Head r}
    (steps : ReducesStar M.realizers.rules (appSpine (.const c) us) w) :
    ∃ us', w = appSpine (.const c) us' ∧ List.Forall₂ (ReducesStar M.realizers.rules) us us' := by
  induction steps with
  | refl => exact ⟨us, rfl, List.forall₂_refl us⟩
  | tail _ step ih =>
      obtain ⟨us', rfl, pointwise⟩ := ih
      obtain ⟨pre, a, a', post, rfl, s, rfl⟩ :=
        constSpine_reduct M.realizers.shape (fun arity inspect role => (stuck arity inspect role).elim)
          step
      exact ⟨pre ++ a' :: post, rfl, forall₂_reducesStar_step s pre pointwise⟩

/-- **A constructor applied to realizers of the candidates of its fields lies in the
constructor candidate**: it reduces only in its arguments, so it reaches no other
constructor, and its arguments stay in their candidates. -/
theorem ctorCand_spine {T k : DeclName} {cs : List (DeclName × List (Field Head))}
    (realRole : M.realizers.roles T = .inductive cs)
    (realDeclared : ConstructorsDeclared M.realizers.roles) {fs : List (Field Head)}
    (mem : (k, fs) ∈ cs) {r : Nat} {Xs : List M.Cand} {us : List (Tm Head r)}
    (reals : List.Forall₂ (fun (X : M.Cand) (u : Tm Head r) => X.mem u) Xs us) :
    (ctorCand M.realizers T k Xs).mem (appSpine (.const k) us) := by
  have stuck : ∀ arity inspect, M.realizers.roles k ≠ .computes arity inspect := by
    intro _ _ h
    rw [realDeclared.arity realRole mem] at h
    cases h
  refine ⟨SN.constSpine M.realizers.shape (fun _ _ h => (stuck _ _ h).elim) (forall₂_mem_sn reals),
    fun k' fs' _ ne us' reach => ?_, fun us' reach => ?_⟩
  · obtain ⟨us'', e, -⟩ := reducesStar_constSpine stuck reach.2.2
    exact ne (appSpine_const_injective e).1
  · obtain ⟨us'', e, pointwise⟩ := reducesStar_constSpine stuck reach.2.2
    obtain ⟨-, rfl⟩ := appSpine_const_injective e
    exact forall₂_mem_reducts reals pointwise

/-! ## The type -/

/-- **A simple inductive type is a valid term of its universe**: at every world it is
interpreted at the universe's level by its inductive pack, over the given packs of its closed
field types, and it is a type constant of the shape of itself. -/
theorem ValidTmS.inductiveType (laws : M.Laws) {T : DeclName}
    {cs : List (DeclName × List (Field Head))} (role : M.roles T = .inductive cs)
    (realRole : M.realizers.roles T = .inductive cs) {u : Head} (hu : M.rules.isUniverse u)
    (field : ∀ {m : Nat}, World M.reading m → Tm Head 0 → Pack M.value m)
    (fieldInterp : ∀ {m : Nat} (ξ : World M.reading m) {F : Tm Head 0}, F ∈ closedFields cs →
      InterpAt M.value (M.levels.level u) ξ (liftClosed F) (field ξ F)) :
    ValidTmS M .nil (.const T) (.head u) := by
  refine ⟨ValidTyS.sort hu, fun {_ _ ξ _ _ _} _ {P} den => ?_⟩
  rw [DenS.sort_inv laws hu den]
  have interp : ∀ {m : Nat} (ξ' : World M.reading m),
      InterpAt M.value (M.levels.level u) ξ' (.const T) (indPack M.value T cs (field ξ')) :=
    fun ξ' => SInterp.ind .refl role (field ξ') fun hF => fieldInterp ξ' hF
  refine ⟨fun {_ ξ' _} _ => ⟨_, interp ξ', interp ξ', .const (.inr ⟨_, role⟩) .refl .refl⟩, ?_⟩
  exact SN.constSpine M.realizers.shape (args := [])
    (fun _ _ h => by rw [realRole] at h; cases h) (by simp)

/-! ## The constructors -/

/-- Fields related with realizers, extended at the end. -/
theorem FieldsS.snoc {n r : Nat} {ξ : World M.reading n} {T : DeclName} :
    ∀ {fs : List (Field Head)} {as as' : List (Tm Head n)} {us : List (Tm Head r)},
      FieldsS ξ T fs as as' us → ∀ {f : Field Head} {a a' : Tm Head n} {u : Tm Head r},
      (∀ {PA : Pack M.value n}, DenS M.value ξ (liftClosed (f.type T)) PA → Rel3 PA a a' u) →
      FieldsS ξ T (fs ++ [f]) (as ++ [a]) (as' ++ [a']) (us ++ [u])
  | _, _, _, _, .nil, _, _, _, _, h => .cons h .nil
  | _, _, _, _, .cons h₀ rest, _, _, _, _, h => .cons h₀ (FieldsS.snoc rest h)

/-- **Related valuations of a constructor's telescope relate its fields**, each at the
denotation of its type, with realizers. -/
theorem EqSubstS.ctorFields (laws : M.Laws) {T : DeclName} {fs : List (Field Head)} :
    ∀ (j : Nat), j ≤ fs.length → ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head j m}
      {ς : Sub Head j r}, EqSubstS M (ofEntries (ctorEntry T fs) j) ξ σ σ' ς →
      FieldsS ξ T (fs.take j) (telescopeArgs (ofEntries (ctorEntry T fs) j) σ)
        (telescopeArgs (ofEntries (ctorEntry T fs) j) σ')
        (telescopeArgs (ofEntries (ctorEntry T fs) j) ς)
  | 0, _, _, _, _, _, _, _, _ => .nil
  | j + 1, hj, _, _, ξ, σ, σ', ς, e => by
      obtain ⟨tail, P, denP, rel, real⟩ := e
      have rest := EqSubstS.ctorFields laws j (by omega) tail
      have entry : Presentation.subst (tailSub σ) (ctorEntry T fs j) =
          liftClosed (fs[j].type T) := by
        rw [ctorEntry, subst_liftClosed, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
          Option.getD_some]
      rw [entry] at denP
      rw [List.take_succ_eq_append_getElem (by omega)]
      exact FieldsS.snoc rest fun den => by
        rw [DenS.deterministic laws.value den denP]
        exact ⟨rel, real⟩


section Fields

variable {n r : Nat} {ξ : World M.reading n} {T : DeclName}
  {cs : List (DeclName × List (Field Head))} {field : Tm Head 0 → Pack M.value n}
  (hT : DenS M.value ξ (.const T) (indPack M.value T cs field))
  (hF : ∀ {F : Tm Head 0}, F ∈ closedFields cs → DenS M.value ξ (liftClosed F) (field F))
include hT hF

/-- Fields related at the denotations of their types are related at the inductive type's
fields. -/
theorem FieldsS.indFields :
    ∀ {fs : List (Field Head)} {as as' : List (Tm Head n)} {us : List (Tm Head r)},
      FieldsS ξ T fs as as' us → (∀ {F : Tm Head 0}, Field.closed F ∈ fs → F ∈ closedFields cs) →
      IndFields M.value cs field fs as as'
  | _, _, _, _, .nil, _ => .nil
  | .recursive :: _, _, _, _, .cons h rest, closed =>
      .recursive (h hT).1 (FieldsS.indFields rest fun hF' => closed (List.mem_cons_of_mem _ hF'))
  | .closed _ :: _, _, _, _, .cons h rest, closed =>
      .closed (h (hF (closed List.mem_cons_self))).1
        (FieldsS.indFields rest fun hF' => closed (List.mem_cons_of_mem _ hF'))

/-- The realizers of related fields realize the candidates of every shape of the fields. -/
theorem FieldsS.reals :
    ∀ {fs : List (Field Head)} {as as' : List (Tm Head n)} {us : List (Tm Head r)}
      {fields : IndShapes Head n}, FieldsS ξ T fs as as' us →
      HasIndShapes M.value cs fs as fields →
      (∀ {F : Tm Head 0}, Field.closed F ∈ fs → F ∈ closedFields cs) →
      List.Forall₂ (fun (X : M.Cand) (u : Tm Head r) => X.mem u)
        (IndShapes.reals M.value T field fields) us
  | _, _, _, _, _, .nil, .nil, _ => .nil
  | .recursive :: _, _, _, _, _, .cons h rest, .recursive shape shapes, closed =>
      .cons (((KCand.mem_inter M.realizers.reflects _).mp (h hT).2).2 ⟨_, shape⟩)
        (FieldsS.reals rest shapes fun hF' => closed (List.mem_cons_of_mem _ hF'))
  | .closed _ :: _, _, _, _, _, .cons h rest, .closed shapes, closed =>
      .cons (h (hF (closed List.mem_cons_self))).2
        (FieldsS.reals rest shapes fun hF' => closed (List.mem_cons_of_mem _ hF'))

/-- The realizers of related fields are strongly normalizing. -/
theorem FieldsS.sn :
    ∀ {fs : List (Field Head)} {as as' : List (Tm Head n)} {us : List (Tm Head r)},
      FieldsS ξ T fs as as' us → (∀ {F : Tm Head 0}, Field.closed F ∈ fs → F ∈ closedFields cs) →
      ∀ u ∈ us, SN M.realizers.rules u
  | _, _, _, _, .nil, _ => fun _ h => nomatch h
  | .recursive :: _, _, _, _, .cons h rest, closed => fun u hu => by
      rcases List.mem_cons.mp hu with rfl | hu
      · exact KCand.sn _ (h hT).2
      · exact FieldsS.sn rest (fun hF' => closed (List.mem_cons_of_mem _ hF')) u hu
  | .closed _ :: _, _, _, _, .cons h rest, closed => fun u hu => by
      rcases List.mem_cons.mp hu with rfl | hu
      · exact KCand.sn _ (h (hF (closed List.mem_cons_self))).2
      · exact FieldsS.sn rest (fun hF' => closed (List.mem_cons_of_mem _ hF')) u hu

end Fields

/-- **A constructor is a valid term of its declared type**: applied to related fields it is
related to itself applied to the other fields, by the clause of the constructor, and applied to
realizers of the fields it realizes every shape of the value. The validity of the declared type
and of its parts are hypotheses, which the fundamental lemma of a smaller stage provides. -/
theorem ValidTmS.inductiveCtor (laws : M.Laws) {T : DeclName}
    {cs : List (DeclName × List (Field Head))} (role : M.roles T = .inductive cs)
    (realRole : M.realizers.roles T = .inductive cs)
    (realDeclared : ConstructorsDeclared M.realizers.roles) {k : DeclName}
    {fs : List (Field Head)} (mem : (k, fs) ∈ cs)
    (validType : ValidTyS M .nil (ctorType T fs)) (partsType : StructuredS M .nil (ctorType T fs)) :
    ValidTmS M .nil (.const k) (ctorType T fs) := by
  obtain ⟨_, validResult, _⟩ :=
    ValidTyS.close_parts (ctorTele T fs) (C := .const T) validType partsType
  refine ValidTmS.close laws (ctorTele T fs) (C := .const T) (f := .const k) validType partsType
    ⟨validResult, fun {_ _ ξ σ σ' ς} e {P} den => ?_⟩
  have fieldsS := EqSubstS.ctorFields laws fs.length le_rfl e
  rw [List.take_length] at fieldsS
  change DenS M.value ξ (.const T) P at den
  obtain ⟨field, rfl, hF⟩ := DenS.ind_inv laws.value den role
  have closed : ∀ {F : Tm Head 0}, Field.closed F ∈ fs → F ∈ closedFields cs :=
    fun hF' => mem_closedFields mem hF'
  rw [subst_applyClosed_const, subst_applyClosed_const, subst_applyClosed_const]
  refine ⟨.ctor mem .refl .refl (FieldsS.indFields den hF fieldsS closed), ?_⟩
  refine (KCand.mem_inter M.realizers.reflects _).mpr ⟨SN.constSpine M.realizers.shape
    (fun _ _ h => by rw [realDeclared.arity realRole mem] at h; cases h)
    (FieldsS.sn den hF fieldsS closed), fun ⟨s, hs⟩ => ?_⟩
  cases hs with
  | ctor mem' red shapes =>
      have e := laws.value.unique red .refl (laws.value.ctorSpine_whnf role mem' _)
        (laws.value.ctorSpine_whnf role mem _)
      obtain ⟨rfl, rfl⟩ := appSpine_const_injective e
      obtain rfl := laws.value.declared.fields_unique role mem mem'
      exact ctorCand_spine realRole realDeclared mem (FieldsS.reals den hF fieldsS shapes closed)
  | star red daimonic =>
      exact (laws.value.ctorSpine_not_daimonic role mem .refl red daimonic).elim

/-! ## The recursor -/

/-- Methods over the motive `p`, one for each constructor, related at their case types, with
realizers. -/
def MethodsS {n r : Nat} (ξ : World M.reading n) (T : DeclName) (p : Tm Head n)
    (cs : List (DeclName × List (Field Head))) (ms ms' : List (Tm Head n))
    (ms₀ : List (Tm Head r)) : Prop :=
  ms.length = cs.length ∧ ms'.length = cs.length ∧ ms₀.length = cs.length ∧
    ∀ {i : Nat} {k : DeclName} {fs : List (Field Head)}, cs[i]? = some (k, fs) →
      ∃ g g' g₀ PM, ms[i]? = some g ∧ ms'[i]? = some g' ∧ ms₀[i]? = some g₀ ∧
        DenS M.value ξ (caseType T k fs p) PM ∧ Rel3 PM g g' g₀

namespace MethodsS

variable {n r : Nat} {ξ : World M.reading n} {T : DeclName} {p : Tm Head n}

theorem nil : MethodsS (r := r) ξ T p [] [] [] [] :=
  ⟨rfl, rfl, rfl, fun h => nomatch h⟩

theorem snoc {cs : List (DeclName × List (Field Head))} {ms ms' : List (Tm Head n)}
    {ms₀ : List (Tm Head r)} (methods : MethodsS ξ T p cs ms ms' ms₀) {k : DeclName}
    {fs : List (Field Head)} {g g' : Tm Head n} {g₀ : Tm Head r} {PM : Pack M.value n}
    (den : DenS M.value ξ (caseType T k fs p) PM) (rel : Rel3 PM g g' g₀) :
    MethodsS ξ T p (cs ++ [(k, fs)]) (ms ++ [g]) (ms' ++ [g']) (ms₀ ++ [g₀]) := by
  obtain ⟨l, l', l₀, get⟩ := methods
  refine ⟨by simp [l], by simp [l'], by simp [l₀], fun {i k' fs'} hi => ?_⟩
  rcases Nat.lt_or_ge i cs.length with lt | ge
  · rw [List.getElem?_append_left lt] at hi
    obtain ⟨h, h', h₀, PM', hh, hh', hh₀, d, rel'⟩ := get hi
    exact ⟨h, h', h₀, PM', by rw [List.getElem?_append_left (l ▸ lt), hh],
      by rw [List.getElem?_append_left (l' ▸ lt), hh'],
      by rw [List.getElem?_append_left (l₀ ▸ lt), hh₀], d, rel'⟩
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
        exact ⟨g, g', g₀, PM, by rw [List.getElem?_append_right (by omega)]; simp [l],
          by rw [List.getElem?_append_right (by omega)]; simp [l'],
          by rw [List.getElem?_append_right (by omega)]; simp [l₀], den, rel⟩

/-- Methods related to others are related to themselves. -/
theorem left (laws : M.Laws) {cs : List (DeclName × List (Field Head))}
    {ms ms' : List (Tm Head n)} {ms₀ : List (Tm Head r)} (methods : MethodsS ξ T p cs ms ms' ms₀) :
    MethodsS ξ T p cs ms ms ms₀ := by
  obtain ⟨l, -, l₀, get⟩ := methods
  refine ⟨l, l, l₀, fun hi => ?_⟩
  obtain ⟨g, g', g₀, PM, hg, -, hg₀, den, rel⟩ := get hi
  exact ⟨g, g, g₀, PM, hg, hg, hg₀, den, DenS.refl_left laws.value den rel.1, rel.2⟩

/-- Related methods with realizers are related methods. -/
theorem values {cs : List (DeclName × List (Field Head))} {ms ms' : List (Tm Head n)}
    {ms₀ : List (Tm Head r)} (methods : MethodsS ξ T p cs ms ms' ms₀) :
    MethodsV ξ T p cs ms ms' := by
  obtain ⟨l, l', _, get⟩ := methods
  refine ⟨l, l', fun hi => ?_⟩
  obtain ⟨g, g', _, PM, hg, hg', _, den, rel⟩ := get hi
  exact ⟨g, g', PM, hg, hg', den, rel.1⟩

/-- The realizers of methods stay realizers along their reductions. -/
theorem reducts {cs : List (DeclName × List (Field Head))} {ms ms' : List (Tm Head n)}
    {ms₀ ms₀' : List (Tm Head r)} (methods : MethodsS ξ T p cs ms ms' ms₀)
    (steps : List.Forall₂ (ReducesStar M.realizers.rules) ms₀ ms₀') :
    MethodsS ξ T p cs ms ms' ms₀' := by
  obtain ⟨l, l', l₀, get⟩ := methods
  refine ⟨l, l', (List.Forall₂.length_eq steps).symm.trans l₀, fun hi => ?_⟩
  obtain ⟨g, g', g₀, PM, hg, hg', hg₀, den, rel⟩ := get hi
  have hi' : _ < ms₀.length := (List.getElem?_eq_some_iff.mp hg₀).1
  obtain ⟨g₀', hg₀', step⟩ : ∃ g₀', ms₀'[_]? = some g₀' ∧ ReducesStar M.realizers.rules g₀ g₀' := by
    have h := List.forall₂_iff_get.mp steps
    refine ⟨ms₀'[_]'(h.1 ▸ hi'), List.getElem?_eq_getElem _, ?_⟩
    have e := (List.getElem?_eq_some_iff.mp hg₀).2
    have := h.2 _ hi' (h.1 ▸ hi')
    simp only [List.get_eq_getElem] at this
    rw [e] at this
    exact this
  exact ⟨g, g', g₀', PM, hg, hg', hg₀', den, rel.1, KCand.reducts _ rel.2 step⟩

/-- The realizers of methods are strongly normalizing. -/
theorem sn {cs : List (DeclName × List (Field Head))} {ms ms' : List (Tm Head n)}
    {ms₀ : List (Tm Head r)} (methods : MethodsS ξ T p cs ms ms' ms₀) :
    ∀ g₀ ∈ ms₀, SN M.realizers.rules g₀ := by
  intro g₀ hg₀
  obtain ⟨l, -, l₀, get⟩ := methods
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg₀
  obtain ⟨⟨k, fs⟩, hc⟩ : ∃ c, cs[i]? = some c := ⟨cs[i]'(l₀ ▸ hi), List.getElem?_eq_getElem _⟩
  obtain ⟨_, _, g₀', _, _, _, hg₀', _, rel⟩ := get hc
  rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hg₀'
  rw [hg₀']
  exact KCand.sn _ rel.2

end MethodsS

/-- The recursive shapes among the shapes of fields. -/
def recursiveShapes {n : Nat} : IndShapes Head n → List (IndShape Head n)
  | .nil => []
  | .recursive s rest => s :: recursiveShapes rest
  | .closed _ _ rest => recursiveShapes rest

/-! ## The realizers of the recursor -/

/-- The values of a shape, related to themselves, with a denotation of the motive there. -/
abbrev RecPoint {n : Nat} (ξ : World M.reading n) (cs : List (DeclName × List (Field Head)))
    (field : Tm Head 0 → Pack M.value n) (P : Tm Head n) (s : IndShape Head n) : Type :=
  (t : Tm Head n) ×' (Q : Pack M.value n) ×'
    (HasIndShape M.value cs t s ∧ IndRel M.value cs field t t ∧ DenS M.value ξ (.app P t) Q)

/-- **The realizers of the recursor's values at the values of a shape**: at every value of the
shape and every denotation of the motive there, the realizers of the recursor's value. -/
def recFamily {n : Nat} (ξ : World M.reading n) (cs : List (DeclName × List (Field Head)))
    (field : Tm Head 0 → Pack M.value n) (rec : DeclName) (P : Tm Head n) (ms : List (Tm Head n))
    (s : IndShape Head n) : M.Cand :=
  KCand.inter M.realizers.reflects fun x : RecPoint ξ cs field P s =>
    x.2.1.real (recApp rec (P :: ms) x.1)

/-- The recursor at a shape: applied to a strongly normalizing motive, realizers of the
methods and a realizer of the shape, it realizes the recursor's values at that shape. -/
def RecClaim {n : Nat} (ξ : World M.reading n) (T rec : DeclName)
    (cs : List (DeclName × List (Field Head))) (field : Tm Head 0 → Pack M.value n)
    (P : Tm Head n) (ms : List (Tm Head n)) (r : Nat) (s : IndShape Head n) : Prop :=
  ∀ {p₀ : Tm Head r} {ms₀ : List (Tm Head r)} {a : Tm Head r}, SN M.realizers.rules p₀ →
    MethodsS ξ T P cs ms ms ms₀ → (s.real M.value T field).mem a →
      (recFamily ξ cs field rec P ms s).mem (recApp rec (p₀ :: ms₀) a)

section Realizers

variable (laws : M.Laws) {T rec : DeclName} {cs : List (DeclName × List (Field Head))}
  (decl : InductiveIn M T rec cs) {n : Nat} {ξ : World M.reading n}
  {field : Tm Head 0 → Pack M.value n}
  (hT : DenS M.value ξ (.const T) (indPack M.value T cs field))
  (hF : ∀ {F : Tm Head 0}, F ∈ closedFields cs → DenS M.value ξ (liftClosed F) (field F))
  {v : Head} (hv : M.rules.isUniverse v) {RP : Pack M.value n}
  (denP : DenS M.value ξ (.pi (.const T) (.head v)) RP) {P : Tm Head n} (relP : RP.rel P P)
  {ms : List (Tm Head n)} {r : Nat}
include laws decl hT hF hv denP relP

/-- The fields of a value of a shape, with realizers of the shapes of its fields: the fields are
related with their realizers, and the recursive calls at them are related with the recursor
applied to the realizers, when the claim holds at the recursive shapes. -/
theorem hyps_of_claims {p₀ : Tm Head r} {ms₀ : List (Tm Head r)} (sp : SN M.realizers.rules p₀)
    (methods : MethodsS ξ T P cs ms ms ms₀) :
    ∀ {fs : List (Field Head)} {as : List (Tm Head n)} {fields : IndShapes Head n}
      {us : List (Tm Head r)}, HasIndShapes M.value cs fs as fields →
      IndFields M.value cs field fs as as →
      (∀ {F : Tm Head 0}, Field.closed F ∈ fs → F ∈ closedFields cs) →
      (∀ s ∈ recursiveShapes fields, RecClaim ξ T rec cs field P ms r s) →
      List.Forall₂ (fun (X : M.Cand) (u : Tm Head r) => X.mem u)
        (IndShapes.reals M.value T field fields) us →
      HypsS ξ P (recArgs fs as) ((recArgs fs as).map (recApp rec (P :: ms)))
        ((recArgs fs as).map (recApp rec (P :: ms))) ((recArgs fs us).map (recApp rec (p₀ :: ms₀))) ∧
      FieldsS ξ T fs as as us := by
  intro fs
  induction fs with
  | nil =>
      intro as fields us shapes _ _ _ reals
      cases shapes
      cases reals
      exact ⟨.nil, .nil⟩
  | cons f fs ih =>
      intro as fields us shapes fieldsRel closed claims reals
      cases shapes with
      | recursive shape rest =>
          cases fieldsRel with
          | recursive headRel restRel =>
              cases reals with
              | cons hu restReals =>
                  obtain ⟨hyps, fieldsS⟩ := ih rest restRel
                    (fun hF' => closed (List.mem_cons_of_mem _ hF'))
                    (fun s hs => claims s (List.mem_cons_of_mem _ hs)) restReals
                  have claim := claims _ List.mem_cons_self sp methods hu
                  refine ⟨.cons (fun den => ⟨ValueSide.rec_related decl.values laws.value hT hF
                      hv denP relP methods.values headRel den,
                      ((KCand.mem_inter M.realizers.reflects _).mp claim).2
                        ⟨_, _, shape, headRel, den⟩⟩) hyps, .cons (fun d => ?_) fieldsS⟩
                  rw [DenS.deterministic laws.value d hT]
                  refine ⟨headRel, ?_⟩
                  rw [indPack_real_of_shape laws.value decl.role shape]
                  exact hu
      | closed rest =>
          cases fieldsRel with
          | closed hRel restRel =>
              cases reals with
              | cons hu restReals =>
                  obtain ⟨hyps, fieldsS⟩ := ih rest restRel
                    (fun hF' => closed (List.mem_cons_of_mem _ hF')) claims restReals
                  refine ⟨hyps, .cons (fun d => ?_) fieldsS⟩
                  rw [DenS.deterministic laws.value d (hF (closed List.mem_cons_self))]
                  exact ⟨hRel, hu⟩

/-- **The realizers of the recursor**, by induction on the derivation of the shape of a value:
a realizer of a constructor shape reaches only that constructor, with fields realizing the
shapes of the fields, so the recursor's root reducts are the method's realizer applied to them
and to the recursive calls; a realizer of the daimon's shape reaches no constructor, so the
recursor never computes. -/
theorem rec_claim : ∀ {t₀ : Tm Head n} {s : IndShape Head n}, HasIndShape M.value cs t₀ s →
    IndRel M.value cs field t₀ t₀ → RecClaim ξ T rec cs field P ms r s := by
  intro t₀ s h
  refine HasIndShape.rec
    (motive_1 := fun t₀ s _ => IndRel M.value cs field t₀ t₀ → RecClaim ξ T rec cs field P ms r s)
    (motive_2 := fun fs as fields _ => IndFields M.value cs field fs as as →
      (∀ {F : Tm Head 0}, Field.closed F ∈ fs → F ∈ closedFields cs) →
        ∀ s ∈ recursiveShapes fields, RecClaim ξ T rec cs field P ms r s)
    ?_ ?_ ?_ ?_ ?_ h
  · intro k fs t₀ as₀ fields mem red₀ shapes₀ ih valid p₀ ms₀ a sp methods ha
    have claims := ih (IndRel.val_fields decl.values laws.value valid mem red₀)
      (fun hF' => mem_closedFields mem hF')
    refine KCand.computingSpine_mem M.realizers.shape _ decl.realRecRole
      (args := p₀ :: ms₀ ++ [a]) (by simp [methods.2.2.1]) ?_ ?_
    · intro b hb
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | hb | rfl
      · exact sp
      · exact methods.sn b hb
      · exact KCand.sn _ ha
    · intro args' steps res step
      obtain ⟨p'', ms'', i, k', fs', us', g'', hlen, hi, hus, hg'', e, rfl⟩ := decl.realIota step
      obtain ⟨-, eArgs⟩ := appSpine_const_injective e
      have pw := ArgsStep.star_forall₂ steps
      rw [eArgs] at pw
      obtain ⟨pwPre, pwLast⟩ := forall₂_append_inv pw (by simp [methods.2.2.1, hlen])
      obtain ⟨hp, pwMs⟩ := List.forall₂_cons.mp pwPre
      obtain ⟨ha', -⟩ := List.forall₂_cons.mp pwLast
      have mem' : (k', fs') ∈ cs := List.mem_of_getElem? hi
      have reach : Reaches M.realizers k' fs'.length a us' :=
        ⟨decl.realDeclared.arity decl.realRole mem', hus, ha'⟩
      have hk : k' = k := by
        by_cases hk : k' = k
        · exact hk
        · exact (ha.2.1 k' fs' (by rw [ctorsOf_of_inductive decl.realRole]; exact mem') hk us'
            reach).elim
      subst hk
      have hfs : fs' = fs := decl.realDeclared.fields_unique decl.realRole mem' mem
      subst hfs
      have reachX : Reaches M.realizers k' (IndShapes.reals M.value T field fields).length a us' := by
        rw [HasIndShapes.reals_length T field shapes₀]
        exact reach
      have usReals := ha.2.2 us' reachX
      have methods'' := methods.reducts pwMs
      have sp'' : SN M.realizers.rules p'' := sp.reducts hp
      have pointMem : ∀ x : RecPoint ξ cs field P (.ctor k' fields),
          (x.2.1.real (recApp rec (P :: ms) x.1)).mem
            (appSpine g'' (us' ++ (recArgs fs' us').map (recApp rec (p'' :: ms'')))) := by
        rintro ⟨t, Q, shape, val, den⟩
        cases shape with
        | @ctor _ fsT _ as _ memT redT shapesT =>
            have hfsT : fsT = fs' := laws.value.declared.fields_unique decl.role memT mem'
            subst hfsT
            have valT := IndRel.val_fields decl.values laws.value val memT redT
            obtain ⟨hyps, fieldsS⟩ := hyps_of_claims laws decl hT hF hv denP relP sp'' methods''
              shapesT valT (fun hF' => mem_closedFields memT hF') claims usReals
            obtain ⟨g, g', g₀, PM, hg, hg', hg₀, denM, relM⟩ := methods''.2.2.2 hi
            have eg : g₀ = g'' := Option.some.inj (hg₀.symm.trans hg'')
            subst eg
            have eg' : g = g' := Option.some.inj (hg.symm.trans hg')
            subst eg'
            obtain ⟨R', denR', rel3⟩ := method_app laws fieldsS hyps denM relM
            have toCtor : IndRel M.value cs field t (appSpine (.const k') as) :=
              .ctor memT redT .refl valT
            obtain ⟨R₀, den₀, denCtor⟩ := ValueSide.motive_den laws.value hT hv denP relP toCtor
            have eQ : Q = R' := (DenS.deterministic laws.value den den₀).trans
              (DenS.deterministic laws.value denCtor denR')
            subst eQ
            have relRec : Q.rel (recApp rec (P :: ms) t)
                (appSpine g (as ++ (recArgs fsT as).map (recApp rec (P :: ms)))) :=
              (DenS.expansive laws.value den).left
                (ValueSide.rec_red_ctor decl.values methods''.1 hi hg (IndFields.length valT).1
                  redT) rel3.1
            rw [DenS.real_eq_of_rel laws.value den relRec]
            exact rel3.2
      obtain ⟨Q₀, den₀, -⟩ := ValueSide.motive_den laws.value hT hv denP relP valid
      exact (KCand.mem_inter M.realizers.reflects _).mpr
        ⟨KCand.sn _ (pointMem ⟨t₀, Q₀, .ctor mem red₀ shapes₀, valid, den₀⟩), pointMem⟩
  · intro t₀ u red daimonic _ p₀ ms₀ a sp methods ha
    refine KCand.computingSpine_mem M.realizers.shape _ decl.realRecRole
      (args := p₀ :: ms₀ ++ [a]) (by simp [methods.2.2.1]) ?_ ?_
    · intro b hb
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | hb | rfl
      · exact sp
      · exact methods.sn b hb
      · exact KCand.sn _ ha
    · intro args' steps res step
      obtain ⟨p'', ms'', i, k', fs', us', g'', hlen, hi, hus, hg'', e, rfl⟩ := decl.realIota step
      obtain ⟨-, eArgs⟩ := appSpine_const_injective e
      have pw := ArgsStep.star_forall₂ steps
      rw [eArgs] at pw
      obtain ⟨-, pwLast⟩ := forall₂_append_inv pw (by simp [methods.2.2.1, hlen])
      obtain ⟨ha', -⟩ := List.forall₂_cons.mp pwLast
      have mem' : (k', fs') ∈ cs := List.mem_of_getElem? hi
      exact (ha.2 k' fs' (by rw [ctorsOf_of_inductive decl.realRole]; exact mem') us'
        ⟨decl.realDeclared.arity decl.realRole mem', hus, ha'⟩).elim
  · intro _ _ s hs
    exact nomatch hs
  · intro fs a as shape rest _ _ ih ihRest fieldsRel closed s hs
    cases fieldsRel with
    | recursive headRel restRel =>
        rcases List.mem_cons.mp hs with rfl | hs
        · exact ih headRel
        · exact ihRest restRel (fun hF' => closed (List.mem_cons_of_mem _ hF')) s hs
  · intro F fs a as rest _ ihRest fieldsRel closed s hs
    cases fieldsRel with
    | closed _ restRel => exact ihRest restRel (fun hF' => closed (List.mem_cons_of_mem _ hF')) s hs

end Realizers

/-! ## Validity of the recursor -/

/-- **Related valuations of the recursor's prefix**: the motive at `T → v` and the methods at
their case types, related with realizers. -/
theorem EqSubstS.recPrefix (laws : M.Laws) {T : DeclName} {v : Head}
    {cs : List (DeclName × List (Field Head))} :
    ∀ (j : Nat), j ≤ cs.length → ∀ {m r : Nat} {ξ : World M.reading m}
      {τ τ' : Sub Head (j + 1) m} {ς : Sub Head (j + 1) r},
      EqSubstS M (ofEntries (recEntry T v cs) (j + 1)) ξ τ τ' ς →
      (∃ RP, DenS M.value ξ (.pi (.const T) (.head v)) RP ∧
        Rel3 RP (τ (Fin.last j)) (τ' (Fin.last j)) (ς (Fin.last j))) ∧
      ∃ ms ms' ms₀, telescopeArgs (ofEntries (recEntry T v cs) (j + 1)) τ = τ (Fin.last j) :: ms ∧
        telescopeArgs (ofEntries (recEntry T v cs) (j + 1)) τ' = τ' (Fin.last j) :: ms' ∧
        telescopeArgs (ofEntries (recEntry T v cs) (j + 1)) ς = ς (Fin.last j) :: ms₀ ∧
        MethodsS ξ T (τ (Fin.last j)) (cs.take j) ms ms' ms₀
  | 0, _, _, _, ξ, τ, τ', ς, e => by
      obtain ⟨-, RP, den, rel, real⟩ := e
      exact ⟨⟨RP, den, rel, real⟩, [], [], [], rfl, rfl, rfl, MethodsS.nil⟩
  | j + 1, hj, _, _, ξ, τ, τ', ς, e => by
      obtain ⟨tail, PM, denM, rel, real⟩ := e
      obtain ⟨motive, ms, ms', ms₀, hms, hms', hms₀, methods⟩ :=
        EqSubstS.recPrefix laws j (by omega) tail
      have hget : cs[j]? = some cs[j] := List.getElem?_eq_getElem (by omega)
      rcases hc : cs[j] with ⟨k, fs⟩
      rw [hc] at hget
      rw [recEntry_method T v cs hget, subst_caseType] at denM
      refine ⟨motive, ms ++ [τ 0], ms' ++ [τ' 0], ms₀ ++ [ς 0], ?_, ?_, ?_, ?_⟩
      · rw [telescopeArgs_ofEntries_succ, hms]
        rfl
      · rw [telescopeArgs_ofEntries_succ, hms']
        rfl
      · rw [telescopeArgs_ofEntries_succ, hms₀]
        rfl
      · rw [List.take_succ_eq_append_getElem (by omega), hc]
        exact methods.snoc denM ⟨rel, real⟩

/-- **The recursor is a valid term of its declared type**, with its motive into the universe
`v`: its values at related arguments are related by induction on the inductive pack
(`rec_related`), and its realizers lie in the meet over the values of a shape
(`rec_claim`). The validity of the declared type and of its parts are hypotheses, which the
fundamental lemma of a smaller stage provides. -/
theorem ValidTmS.inductiveRec (laws : M.Laws) {T rec : DeclName}
    {cs : List (DeclName × List (Field Head))} (decl : InductiveIn M T rec cs) {v : Head}
    (hv : M.rules.isUniverse v) (validType : ValidTyS M .nil (recType T v cs))
    (partsType : StructuredS M .nil (recType T v cs)) :
    ValidTmS M .nil (.const rec) (recType T v cs) := by
  obtain ⟨_, validResult, _⟩ :=
    ValidTyS.close_parts (recTele T v cs) (C := recBody cs.length) validType partsType
  refine ValidTmS.close laws (recTele T v cs) (C := recBody cs.length) (f := .const rec) validType
    partsType ⟨validResult, fun {_ _ ξ σ σ' ς} e {R} den => ?_⟩
  rw [subst_applyClosed_const, subst_applyClosed_const, subst_applyClosed_const]
  obtain ⟨prefixE, PT, denT, relT, realT⟩ := e
  rw [recEntry_scrutinee] at denT
  change DenS M.value ξ (.const T) PT at denT
  obtain ⟨field, rfl, hF⟩ := DenS.ind_inv laws.value denT decl.role
  obtain ⟨⟨RP, denP, relP, realP⟩, ms, ms', ms₀, hms, hms', hms₀, methods⟩ :=
    EqSubstS.recPrefix laws cs.length le_rfl prefixE
  rw [List.take_length] at methods
  have args : ∀ {k : Nat} (τ : Sub Head (cs.length + 2) k),
      telescopeArgs (recTele T v cs) τ =
        telescopeArgs (ofEntries (recEntry T v cs) (cs.length + 1)) (tailSub τ) ++ [τ 0] :=
    fun _ => rfl
  rw [args, args, args, hms, hms', hms₀]
  change DenS M.value ξ (.app (σ (Fin.last (cs.length + 1))) (σ 0)) R at den
  refine ⟨ValueSide.rec_related decl.values laws.value denT hF hv denP relP methods.values relT
    den, ?_⟩
  obtain ⟨s, hs⟩ := IndRel.hasShape relT
  have valid := DenS.refl_left laws.value denT relT
  have ha : (s.real M.value T field).mem (ς 0) := by
    rw [← indPack_real_of_shape laws.value decl.role hs]
    exact realT
  have claim := rec_claim laws decl denT hF hv denP (DenS.refl_left laws.value denP relP) hs valid
    (KCand.sn _ realP) (methods.left laws) ha
  exact ((KCand.mem_inter M.realizers.reflects _).mp claim).2 ⟨_, R, hs, valid, den⟩

end ModelSN
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
