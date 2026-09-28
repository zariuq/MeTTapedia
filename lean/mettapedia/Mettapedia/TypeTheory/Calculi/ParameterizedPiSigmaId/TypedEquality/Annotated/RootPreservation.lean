import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Schemas
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Inversion

/-!
# Preservation of typing by the annotated root steps

`CRootPreserving P`: every annotated root step of `P` preserves typing in formed
contexts, the annotated counterpart of `Normalization.RootPreserving`.

For a rule package annotated from a presentation by schemas
(`ChurchRules.ofSchemas`), preservation holds schema by schema
(`ChurchRules.ofSchemas_rootPreserving`), and a schema preserves typing when the
elaborated right side is typed where the left side's typing puts it
(`SchemaPreserving.of_templateTyped`). The link is **pattern inversion**
(`pattern_inv`), from the injectivity and no-confusion of the type formers: a
typed instance of a first-order left side

* instantiates each metavariable at the type its position requires
  (`patternKnowledge`);
* has the type its left side synthesizes, instantiated, below its own type;
* satisfies the equations its reflexivity positions impose
  (`patternEquations`): the point of a reflexivity proof checked against
  `Id A x y` is equal to `x` and to `y` at `A`.

Every step of the proof follows the elaboration of the left side: the head
constant's declared type, then the domain of each dependent function type it
synthesizes, which the argument's typing matches by injectivity.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open AlgebraicSchema (SchemaFamily SchemaStep)
open Normalization (LevelModel)
open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {R : Rules Head}

/-! ## The statements -/

/-- **The annotated root steps preserve typing** in formed contexts. -/
def CRootPreserving (P : ChurchRules R) : Prop :=
  ∀ {n : Nat} {Γ : CCtx Head n} {l r A : CTm Head n}, CCtxFormed P Γ →
    P.computation.step l r → CTyped P Γ l A → CTyped P Γ r A

/-- The instances of an annotated schema preserve typing. -/
def SchemaPreserving (P : ChurchRules R) {k : Nat} (left right : CTm Head k) : Prop :=
  ∀ {n : Nat} {Γ : CCtx Head n} {σ : CSub Head k n} {A : CTm Head n}, CCtxFormed P Γ →
    CTyped P Γ (left.subst σ) A → CTyped P Γ (right.subst σ) A

/-- **Preservation, schema by schema**, for an annotation derived from a
presentation by schemas. -/
theorem ChurchRules.ofSchemas_rootPreserving (S : SchemaFamily Head)
    (present : Presents R.computation S)
    (schemas : ∀ {k : Nat} {L R' : Tm Head k}, S L R' →
      SchemaPreserving (ChurchRules.ofSchemas R S present)
        (elabLeft (elabDeclarations R.constantType) L)
        (elabRight (elabDeclarations R.constantType) L R')) :
    CRootPreserving (ChurchRules.ofSchemas R S present) := by
  intro n Γ l r A formed step typing
  cases step with
  | instantiate rule σ =>
      obtain ⟨L, R', hS, rfl, rfl⟩ := rule
      exact schemas hS formed typing

/-! ## The equations of reflexivity positions -/

/-- The equations the reflexivity positions of a first-order left side impose:
the point of a reflexivity proof checked against `Id A x y` equals `x` and `y`
at `A`, as triples (point, endpoint, carrier). -/
def patternEquations (decls : DeclName → Option (CTm Head 0)) :
    {k : Nat} → Option (CTm Head k) → Tm Head k → List (CTm Head k × CTm Head k × CTm Head k)
  | _, _, .app f a =>
      patternEquations decls none f ++
        patternEquations decls
          (match (elaborate decls Knowledge.empty none none f).2 with
            | some (.pi D _) => some D
            | _ => none) a
  | _, expected, .refl a =>
      (match expected with
        | some (.id A x y) => [(liftTm a, x, A), (liftTm a, y, A)]
        | _ => []) ++
      patternEquations decls
        (match expected with
          | some (.id A _ _) => some A
          | _ => none) a
  | _, _, _ => []

/-! ## Elaboration of first-order terms -/

/-- A first-order term's elaboration does not read the type of the argument it
is applied to. -/
theorem elaborate_firstOrder_hint (decls : DeclName → Option (CTm Head 0)) {n : Nat}
    {t : Tm Head n} (fo : firstOrder t = true) (K : Knowledge Head n)
    (expected hint : Option (CTm Head n)) :
    elaborate decls K expected hint t = elaborate decls K expected none t := by
  cases t with
  | var => rfl
  | const => rfl
  | head => rfl
  | app => rfl
  | refl => rfl
  | pi => cases fo
  | sigma => cases fo
  | id => cases fo
  | lam => cases fo
  | pair => cases fo
  | fst => cases fo
  | snd => cases fo

/-- The type a first-order application synthesizes. -/
theorem elaborate_app_type (decls : DeclName → Option (CTm Head 0)) {n : Nat}
    {f a : Tm Head n} (fo : firstOrder f = true) (foa : firstOrder a = true) :
    (elaborate decls Knowledge.empty none none (.app f a)).2 =
      match (elaborate decls Knowledge.empty none none f).2 with
      | some (.pi _ B) => some (CTm.inst0 (liftTm a) B)
      | _ => none := by
  simp only [elaborate]
  rw [elaborate_firstOrder_hint decls fo]
  cases h : (elaborate decls Knowledge.empty none none f).2 with
  | none => simp
  | some T => cases T <;> simp [elab_firstOrder decls foa, liftTm]

/-! ## Pattern inversion -/

section Inversion

variable {P : ChurchRules R} (facts : CFormerFacts P) (levels : LevelModel R L)
include facts levels

/-- **Pattern inversion**: a typed instance of a first-order left side, at a type
equal to the instance of the type expected of it, instantiates each metavariable
at the type its position requires, satisfies the equations of its reflexivity
positions, and, unless it is a reflexivity proof, has the type it synthesizes,
instantiated, below its own. -/
theorem pattern_inv {k : Nat} (L : Tm Head k) (fo : firstOrder L = true) :
    ∀ (expected : Option (CTm Head k)) {n : Nat} {Γ : CCtx Head n} (σ : CSub Head k n)
      {X : CTm Head n}, CCtxFormed P Γ → CTyped P Γ ((liftTm L).subst σ) X →
      (∀ E, expected = some E → X = E.subst σ) →
      (∀ i T, patternKnowledge P.constantType expected L i = some T →
        CTyped P Γ (σ i) (T.subst σ)) ∧
      (∀ T, (elaborate P.constantType Knowledge.empty none none L).2 = some T →
        (∀ a, L ≠ .refl a) → CBelow P Γ (T.subst σ) X) ∧
      (∀ e ∈ patternEquations P.constantType expected L,
        CEqual P Γ (e.1.subst σ) (e.2.1.subst σ) (e.2.2.subst σ)) := by
  induction L with
  | var i =>
      intro expected n Γ σ X formed typing hX
      refine ⟨fun j T h => ?_, fun T h _ => ?_, fun e he => ?_⟩
      · simp only [patternKnowledge] at h
        by_cases hj : j = i
        · subst hj
          simp only [ite_true] at h
          rw [← hX T h]
          exact typing
        · simp only [if_neg hj] at h
          cases h
      · simp [elaborate, Knowledge.empty] at h
      · simp [patternEquations] at he
  | const c =>
      intro expected n Γ σ X formed typing hX
      refine ⟨fun j T h => ?_, fun T h _ => ?_, fun e he => ?_⟩
      · simp [patternKnowledge, Knowledge.empty] at h
      · simp only [elaborate] at h
        obtain ⟨type, hc, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨type', u, declared, _, _, le⟩ := typing.generation
        rw [hc] at declared
        cases declared
        rw [CTm.subst_liftClosed]
        exact CTypeLe.toBelow le (CTyped.isType levels typing formed)
      · simp [patternEquations] at he
  | head h =>
      intro expected n Γ σ X formed typing hX
      refine ⟨fun j T h => ?_, fun T h _ => ?_, fun e he => ?_⟩
      · simp [patternKnowledge, Knowledge.empty] at h
      · simp [elaborate] at h
      · simp [patternEquations] at he
  | pi => cases fo
  | sigma => cases fo
  | id => cases fo
  | lam => cases fo
  | pair => cases fo
  | fst => cases fo
  | snd => cases fo
  | app f a ihf iha =>
      simp only [firstOrder, Bool.and_eq_true] at fo
      intro expected n Γ σ X formed typing hX
      obtain ⟨A₀, B₀, tf, ta, le⟩ := typing.generation
      obtain ⟨knowF, synF, eqsF⟩ := ihf fo.1 none σ formed tf (fun _ h => by cases h)
      -- The domain the function's synthesized type gives the argument.
      have hdom : ∀ D B, (elaborate P.constantType Knowledge.empty none none f).2 = some (.pi D B) →
          CTypeEq P Γ (D.subst σ) A₀ ∧ CBelow P (.snoc Γ (D.subst σ)) (B.subst (CTm.liftSub σ)) B₀ := by
        intro D B hf
        have notRefl : ∀ a', f ≠ .refl a' := by
          rintro a' rfl
          simp only [elaborate] at hf
          obtain ⟨_, _, h⟩ := Option.map_eq_some_iff.mp hf
          cases h
        have le' := synF _ hf notRefl
        exact CBelow.pi_parts facts levels le' formed
      refine ⟨fun j T h => ?_, fun T h notRefl => ?_, fun e he => ?_⟩
      · simp only [patternKnowledge, Knowledge.merge] at h
        split at h
        · rename_i T' hT'
          cases h
          exact knowF j _ hT'
        · rename_i hnone
          split at h
          · rename_i D B hf
            obtain ⟨eD, _⟩ := hdom D B hf
            exact (iha fo.2 (some D) σ formed (CTyped.convType ta eD.symm)
              (fun _ h => by cases h; rfl)).1 j T h
          · exact (iha fo.2 none σ formed ta (fun _ h => by cases h)).1 j T h
      · rw [elaborate_app_type P.constantType fo.1 fo.2] at h
        split at h
        · rename_i D B hf
          cases h
          obtain ⟨eD, leB⟩ := hdom D B hf
          have ta' : CTyped P Γ ((liftTm a).subst σ) (D.subst σ) := CTyped.convType ta eD.symm
          have inst := CBelow.instantiate leB ta'
          rw [CTm.subst_inst0]
          exact .subTrans inst (CTypeLe.toBelow le (CTyped.isType levels typing formed))
        · cases h
      · simp only [patternEquations, List.mem_append] at he
        rcases he with he | he
        · exact eqsF e he
        · split at he
          · rename_i D B hf
            obtain ⟨eD, _⟩ := hdom D B hf
            exact (iha fo.2 (some D) σ formed (CTyped.convType ta eD.symm)
              (fun _ h => by cases h; rfl)).2.2 e he
          · exact (iha fo.2 none σ formed ta (fun _ h => by cases h)).2.2 e he
  | refl a ih =>
      intro expected n Γ σ X formed typing hX
      obtain ⟨A₀, ta, le⟩ := typing.generation
      -- The carrier and the equations, when an identity type is expected.
      have hid : ∀ C x y, expected = some (.id C x y) →
          CTyped P Γ ((liftTm a).subst σ) (C.subst σ) ∧
          CEqual P Γ ((liftTm a).subst σ) (x.subst σ) (C.subst σ) ∧
          CEqual P Γ ((liftTm a).subst σ) (y.subst σ) (C.subst σ) := by
        intro C x y hexp
        have hXe : X = (CTm.id C x y).subst σ := hX _ hexp
        have leId := CTypeLe.toBelow le (CTyped.isType levels typing formed)
        rw [hXe] at leId
        have eId := CBelow.id_eq facts levels leId formed
          (CIsType.refl (CBelow.isTypes levels leId formed).1)
        obtain ⟨eC, ex, ey⟩ := CTypeEq.id_injective facts eId formed
        have ta' : CTyped P Γ ((liftTm a).subst σ) (C.subst σ) := CTyped.convType ta eC.symm
        exact ⟨ta', ex.symm, ey.symm⟩
      refine ⟨fun j T h => ?_, fun T _ notRefl => absurd rfl (notRefl a), fun e he => ?_⟩
      · simp only [patternKnowledge] at h
        split at h
        · rename_i C x y
          exact (ih fo (some C) σ formed (hid C x y rfl).1 (fun _ h => by cases h; rfl)).1 j T h
        · exact (ih fo none σ formed ta (fun _ h => by cases h)).1 j T h
      · simp only [patternEquations, List.mem_append] at he
        rcases he with he | he
        · split at he
          · rename_i C x y
            obtain ⟨_, ex, ey⟩ := hid C x y rfl
            simp only [List.mem_cons, List.not_mem_nil, or_false] at he
            rcases he with rfl | rfl
            · exact ex
            · exact ey
          · simp at he
        · split at he
          · rename_i C x y
            exact (ih fo (some C) σ formed (hid C x y rfl).1 (fun _ h => by cases h; rfl)).2.2 e he
          · exact (ih fo none σ formed ta (fun _ h => by cases h)).2.2 e he

/-- **A schema whose elaborated right side is typed preserves typing**: the typing
of an instance of the left side puts the metavariables at the types of the
right side's context and the right side's type below the instance's. -/
theorem SchemaPreserving.of_templateTyped {k : Nat} {L R' : Tm Head k}
    (fo : firstOrder L = true) (notRefl : ∀ a, L ≠ .refl a)
    (typed : TemplateTyped P P.constantType L R') :
    SchemaPreserving P (elabLeft P.constantType L) (elabRight P.constantType L R') := by
  intro n Γ σ A formed typing
  obtain ⟨Θ, T, hK, hT, tR⟩ := typed
  rw [elabLeft_firstOrder P.constantType fo] at typing
  obtain ⟨know, syn, _⟩ := pattern_inv facts levels L fo none σ formed typing (fun _ h => by cases h)
  have mor : CSubstMor P Θ Γ σ := fun i => know i _ (hK i)
  exact .sub (CTyped.substitute tR mor) (syn T hT notRefl)

end Inversion

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
