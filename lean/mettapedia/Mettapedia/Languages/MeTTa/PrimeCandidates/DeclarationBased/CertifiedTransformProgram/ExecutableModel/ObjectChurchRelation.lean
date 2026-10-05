import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectSchemaShapes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationCodes

/-!
# The witness-indexed relation at the object package's eliminator

* **Rigid types** (`objectRigidWith`, `objectRigid`): in every package containing the object
  package, its type of proposition codes, its decoder, the numbers with zero and successor, the
  ground types `set` and the legacy ground head, and declared datatypes with their parameters
  and constructors, the numbers among them. The object package's own rigid types declare the
  numbers only (`objectData`, `objectParams`, `objectCtor`).
* **The eliminator's step** (`RT.objectEliminator`): in every package containing the object
  package's root steps, for every weak-head reduction that reduces the path position of the
  identity eliminator, two eliminator spines `J A x P d y p` and `J A x P d' y p'`
  whose paths are related at the reflexivity tag of `Id A x y` are related at
  `P y p` as far as a token observes, when their methods are. The reflexivity
  clause reduces both paths to `refl r`, `refl r'` with `r ≡ x` and `r ≡ y`; the
  contractum is typed by the eliminator's template under exactly these equations
  (`objectJ_contractum`, from `j_templateTypedEq`, in every package whose universes include
  `U₀`); and head expansion along the eliminator's root step (`objectChurch_jStep`) moves the
  relation back.
* **The quantifier over codes** (`RT.objectAllProp`): for every weak-head reduction
  with these rigid types, `all@prop` is related to itself at `(prop → prop) → prop`
  at every token of the quantifier constant over the universe of codes typed there,
  with the decoding `holds (all@prop f) ⟶ Π (x : prop). holds (f x)` an annotated
  root step (`objectChurch_decodeAllProp`).

Positive example: `objectRigid` is `objectRigidWith` at the object package. Negative example:
a constructor that is not one of the declared datatype's has no relation clause, since
`RigidTypes.ctor` lists the constructors (`RT.tm_ctorTag_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain
open Package (jName)

namespace CodeModel

/-! ## Rigid types -/

/-- **The object package's rigid types in a package containing it**, with declared datatypes
`data`, their parameters `params` and their constructors `ctor`, the numbers among them: the
type of proposition codes and its decoder, the numbers with zero and successor, and the two
ground types, the sets and the legacy ground head, kept apart. -/
def objectRigidWith {R' : Rules Tower.Head} (P : ChurchRules R') (sub : ChurchRulesSub objectChurch P)
    (data : DeclName → Prop) (params : DeclName → List (CTm Tower.Head 0))
    (ctor : DeclName → DeclName → List FieldShape → Prop)
    (ctor_data : ∀ {d c : DeclName} {fs : List FieldShape}, ctor d c fs → data d)
    (zero_ctor : ctor numN zeroN []) (suc_ctor : ctor numN sucN [.self]) : RigidTypes P where
  prop := propN
  holds := holdsN
  num := numN
  zero := zeroN
  suc := sucN
  holds_typed := fun _ => ⟨.sort Tower.zero, sub.isUniverse (.sort _), CDerivable.mono sub holds_typed⟩
  ground := fun g => g = .const setN ∨ g = .head .legacyGround
  data := data
  params := params
  ctor := ctor
  ctor_data := ctor_data
  zero_ctor := zero_ctor
  suc_ctor := suc_ctor

/-- The object package's declared datatypes: the numbers. -/
def objectData : DeclName → Prop := fun d => d = numN

/-- The parameters of the object package's datatypes: none. -/
def objectParams : DeclName → List (CTm Tower.Head 0) := fun _ => []

/-- The constructors of the object package's datatypes: zero and the successor. -/
def objectCtor : DeclName → DeclName → List FieldShape → Prop :=
  fun d c fs => d = numN ∧ (c = zeroN ∧ fs = [] ∨ c = sucN ∧ fs = [.self])

/-- The rigid types of the object package: its declared datatype is the numbers. -/
def objectRigid : RigidTypes objectChurch :=
  objectRigidWith objectChurch (ChurchRulesSub.refl _) objectData objectParams objectCtor
    (fun h => h.1) ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩

/-! ## The eliminator -/

/-- **The eliminator's annotated root step**, at every instance. -/
theorem objectChurch_jStep {n : Nat} (σ : CSub Tower.Head 6 n) :
    objectChurch.computation.step
      (CTm.appSpine (.const jName) [σ 5, σ 4, σ 3, σ 2, σ 1, .refl (σ 0)]) (σ 2) := by
  have s := objectChurch_step_of_spec
    (List.getElem_mem (l := computationSpecs) (n := 3) (by decide))
    (L := eliminatorLeft jName) (R := .var 2) rfl σ
  rw [j_elabLeft, j_elabRight] at s
  exact s

/-- **The eliminator's root step is admitted** along a typed substitution of the
eliminator's context whose point equals the base point and the endpoint: the premises of the
step are the typings of its six arguments and the two equations of its reflexivity
position. -/
theorem objectChurch_jAdmits {R' : Rules Tower.Head} {Q : ChurchRules R'} {n : Nat}
    {Γ : CCtx Tower.Head n} {σ : CSub Tower.Head 6 n} (mor : CSubstMor Q cJTele Γ σ)
    (toPoint : CEqual Q Γ (σ 0) (σ 4) (σ 5)) (toEnd : CEqual Q Γ (σ 0) (σ 1) (σ 5))
    (within : StepsWithin objectChurch Q := by exact objectChurch_within rfl) :
    Q.Admits Γ (CTm.appSpine (.const jName) [σ 5, σ 4, σ 3, σ 2, σ 1, .refl (σ 0)]) (σ 2) := by
  have a := objectChurch_admits_of_spec within
    (List.getElem_mem (l := computationSpecs) (n := 3) (by decide))
    (L := eliminatorLeft jName) (R := .var 2) rfl σ (CSubstMor.patternTypings j_knowledge mor)
    (by
      rw [j_equations]
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact toPoint
      rcases List.mem_cons.1 he with rfl | he
      · exact toEnd
      exact absurd he List.not_mem_nil)
  rw [j_elabLeft, j_elabRight] at a
  exact a

/-- **The contractum of the eliminator is typed under the equations of its
reflexivity position** (`j_templateTypedEq`), in every package whose universes include `U₀`:
at arguments typed by the eliminator's context, whose point equals the base point and the
endpoint, the method has the type `P y (refl a)`. -/
theorem objectJ_contractum {R' : Rules Tower.Head} {P : ChurchRules R'}
    (u0 : R'.isUniverse (.sort Tower.zero)) {n : Nat} {Γ : CCtx Tower.Head n}
    (formed : CCtxFormed P Γ) {σ : CSub Tower.Head 6 n} (mor : CSubstMor P cJTele Γ σ)
    (toPoint : CEqual P Γ (σ 0) (σ 4) (σ 5)) (toEnd : CEqual P Γ (σ 0) (σ 1) (σ 5)) :
    CTyped P Γ (σ 2) (.app (.app (σ 3) (σ 1)) (.refl (σ 0))) := by
  obtain ⟨Θ, T, know, left, typed⟩ := j_templateTypedEq (P := P) u0
  have hΘ : ∀ i, Θ.lookup i = cJTele.lookup i := fun i =>
    Option.some.inj ((know i).symm.trans (j_knowledge i))
  have hT : T = .app (.app (.var 3) (.var 1)) (.refl (.var 0)) :=
    Option.some.inj (left.symm.trans j_leftType)
  have mor' : CSubstMor P Θ Γ σ := fun i => by
    rw [hΘ i]
    exact mor i
  have h := typed formed mor' (by
    rw [j_equations]
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact toPoint
    rcases List.mem_cons.1 he with rfl | he
    · exact toEnd
    exact absurd he List.not_mem_nil)
  rw [j_elabRight, hT] at h
  exact h

section Step

variable {R' : Rules Tower.Head} {P : ChurchRules R'} (within : StepsWithin objectChurch P)
  (u0 : R'.isUniverse (.sort Tower.zero)) {L : Type} [LevelOrder L] (levels : LevelModel R' L)
  {K : RigidTypes P} {H : HeadReduction P K}

/-- The family of the eliminator's last argument, at a path. -/
theorem inst0_motive_family {n : Nat} (M y q : CTm Tower.Head n) :
    CTm.inst0 q (.app (.app (M.rename wk) (y.rename wk)) (.var 0)) = .app (.app M y) q := by
  change CTm.app (.app (CTm.inst0 q (M.rename wk)) (CTm.inst0 q (y.rename wk))) q = _
  rw [CTm.inst0_rename_wk, CTm.inst0_rename_wk]

include within u0 levels in
/-- **The eliminator step of the relation, in a package containing the object package.** Eliminator
spines whose paths are related at the reflexivity tag of `Id A x y`, and whose
methods are related at `P y p` as far as a token observes, are related there. The
contractions use the eliminator's root step and its template's typing under the
equations the reflexivity clause provides; no injectivity of type formers is
used. -/
theorem RT.objectEliminator {n : Nat} {Γ : CCtx Tower.Head n}
    (formed : CCtxFormed P Γ)
    (jPath : ∀ {A x M d y q q' : CTm Tower.Head n}, H.step q q' →
      H.step (.app (CTm.appSpine (.const jName) [A, x, M, d, y]) q)
        (.app (CTm.appSpine (.const jName) [A, x, M, d, y]) q'))
    {A x M d d' y p p' : CTm Tower.Head n} {t : Tok}
    (tA : CTyped P Γ A cU0) (tx : CTyped P Γ x A)
    (tM : CTyped P Γ M (.pi A (.pi (.id (A.rename wk) (x.rename wk) (.var 0)) cU0)))
    (td : CTyped P Γ d (.app (.app M x) (.refl x)))
    (td' : CTyped P Γ d' (.app (.app M x) (.refl x)))
    (ty : CTyped P Γ y A)
    (tS : CTyped P Γ (CTm.appSpine (.const jName) [A, x, M, d, y])
      (.pi (.id A x y) (.app (.app (M.rename wk) (y.rename wk)) (.var 0))))
    (tS' : CTyped P Γ (CTm.appSpine (.const jName) [A, x, M, d', y])
      (.pi (.id A x y) (.app (.app (M.rename wk) (y.rename wk)) (.var 0))))
    (ep : CEqual P Γ p p' (.id A x y))
    (hp : RT H Γ true (.tag .refl) (.id A x y) p p')
    (hd : RT H Γ true t (.app (.app M y) p) d d') :
    RT H Γ true t (.app (.app M y) p) (CTm.appSpine (.const jName) [A, x, M, d, y, p])
      (CTm.appSpine (.const jName) [A, x, M, d', y, p']) := by
  have args : ∀ (e r : CTm Tower.Head n), CTyped P Γ e (.app (.app M x) (.refl x)) →
      CTyped P Γ r A →
        CSubstMor P cJTele Γ
          (CTm.consSub r (CTm.consSub y (CTm.consSub e (CTm.consSub M (CTm.consSub x
            (CTm.consSub A Fin.elim0)))))) := by
    intro e r te tr i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tr
    refine Fin.cases ?_ (fun i => ?_) i
    · exact ty
    refine Fin.cases ?_ (fun i => ?_) i
    · exact te
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tM
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tx
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tA
    exact i.elim0
  have root : ∀ (e r : CTm Tower.Head n), P.computation.step
      (.app (CTm.appSpine (.const jName) [A, x, M, e, y]) (.refl r)) e := fun e r =>
    within.step (objectChurch_jStep (CTm.consSub r (CTm.consSub y (CTm.consSub e (CTm.consSub M
      (CTm.consSub x (CTm.consSub A Fin.elim0)))))))
  have contractum : ∀ (e : CTm Tower.Head n), CTyped P Γ e (.app (.app M x) (.refl x)) →
      ∀ r, CEqual P Γ r x A → CEqual P Γ r y A →
        CTyped P Γ e
          (CTm.inst0 (.refl r) (.app (.app (M.rename wk) (y.rename wk)) (.var 0))) := by
    intro e te r erx ery
    rw [inst0_motive_family]
    exact objectJ_contractum u0 formed (args e r te (CEqual.typed levels erx formed).1) erx ery
  have h := RT.eliminator levels formed (root d) (root d')
    (fun r erx ery =>
      objectChurch_jAdmits (args d r td (CEqual.typed levels erx formed).1) erx ery within)
    (fun r erx ery =>
      objectChurch_jAdmits (args d' r td' (CEqual.typed levels erx formed).1) erx ery within)
    jPath jPath tS tS'
    (contractum d td) (contractum d' td') ep hp (by rw [inst0_motive_family]; exact hd)
  rw [inst0_motive_family] at h
  exact h

end Step

/-! ## The quantifier over proposition codes -/

/-- The quantifier over codes, declared at `(prop → prop) → prop`. -/
theorem allProp_typed {n : Nat} {Γ : CCtx Tower.Head n} :
    CTyped objectChurch Γ (.const allPropN) (.pi (.pi (.const propN) (.const propN)) (.const propN)) :=
  .const (objectDecls_allName .prop) (typeAt_formed (.arr (.arr .prop .prop) .prop) .nil) (.sort _)

/-- The carrier of the quantifier over codes is the type of codes. -/
theorem allProp_carrier : programCodes.decoders.allCarrier allPropN = some (typeTerm .prop) := by
  change (SetProfile.allInstance? allPropN).map typeTerm = _
  rw [SetProfile.allInstance?_allName]
  rfl

/-- The left side of the decoding of a quantified code, elaborated. -/
theorem decodeAllProp_elabLeft : elabLeft objectDecls
    (.app (.const holdsN) (.app (.const allPropN) (.var 0)) : Tower.Tm 1) =
      .app (.const holdsN) (.app (.const allPropN) (.var 0)) := by
  decide

/-- The right side of the decoding of a quantified code, elaborated. -/
theorem decodeAllProp_elabRight : elabRight objectDecls
    (.app (.const holdsN) (.app (.const allPropN) (.var 0)) : Tower.Tm 1)
    (.pi (Presentation.liftClosed (typeTerm .prop))
      (.app (.const holdsN) (.app (Presentation.rename wk (.var 0)) (.var 0)))) =
      .pi (.const propN) (.app (.const holdsN) (.app (.var 1) (.var 0))) := by
  decide

/-- **Decoding a quantified code is an annotated root step**:
`holds (all@prop f) ⟶ Π (x : prop). holds (f x)`. -/
theorem objectChurch_decodeAllProp {n : Nat} (f : CTm Tower.Head n) :
    objectChurch.computation.step (.app (.const holdsN) (.app (.const allPropN) f))
      (.pi (.const propN) (.app (.const holdsN) (.app (f.rename wk) (.var 0)))) := by
  have s := objectChurch_step_of_decoder
    (Or.inr (Or.inl ⟨allPropN, typeTerm .prop, allProp_carrier, rfl⟩)) (fun _ => f)
  have eh : programCodes.decoders.holds = holdsN := rfl
  rw [eh, decodeAllProp_elabLeft, decodeAllProp_elabRight] at s
  exact s

/-- **Decoding a quantified code is admitted where the family is typed** at `prop → prop`. -/
theorem objectChurch_decodeAllProp_admits {R' : Rules Tower.Head} {Q : ChurchRules R'}
    {n : Nat} {Γ : CCtx Tower.Head n} {f : CTm Tower.Head n}
    (typed : CTyped Q Γ f (.pi (.const propN) (.const propN)))
    (same : Q.computation = objectChurch.computation := by rfl) :
    Q.Admits Γ (.app (.const holdsN) (.app (.const allPropN) f))
      (.pi (.const propN) (.app (.const holdsN) (.app (f.rename wk) (.var 0)))) := by
  have a := objectChurch_admits_of_decoder (objectChurch_within same)
    (Or.inr (Or.inl ⟨allPropN, typeTerm .prop, allProp_carrier, rfl⟩)) (Γ := Γ) (fun _ => f)
    (CSubstMor.patternTypings (Θ := .snoc .nil (.pi (.const propN) (.const propN))) (by decide)
      (fun i => by
        obtain rfl : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) i 0
        exact typed))
    (fun e member => by
      have none : patternEquations objectDecls none
          (.app (.const programCodes.decoders.holds) (.app (.const allPropN) (.var 0)) :
            Tower.Tm 1) = [] := by
        decide
      rw [none] at member
      cases member)
  have eh : programCodes.decoders.holds = holdsN := rfl
  rw [eh, decodeAllProp_elabLeft, decodeAllProp_elabRight] at a
  exact a

/-- **The quantifier over codes at its own type of codes, at the object package.**
For every weak-head reduction with the object package's rigid types, every token of
the quantifier constant over the universe of codes typed at `(prop → prop) → prop`
relates `all@prop` to itself there. -/
theorem RT.objectAllProp {L : Type} [LevelOrder L] (levels : LevelModel objectRules L)
    {H : HeadReduction objectChurch objectRigid} {n : Nat} {Γ : CCtx Tower.Head n}
    (formed : CCtxFormed objectChurch Γ) :
    ∀ s, (Ideal.allConst Ideal.codesIdeal).Mem s →
      Ideal.TypedAt (Ideal.cpi (Ideal.cpi Ideal.codesIdeal fun _ => Ideal.codesIdeal)
        fun _ => Ideal.codesIdeal) s →
        RT H Γ true s (.pi (.pi (.const propN) (.const propN)) (.const propN))
          (.const allPropN) (.const allPropN) :=
  RT.allCode levels formed allPropN (u₀ := .sort Tower.zero) (.sort _)
    (const_U0_typed (by decide)) allProp_typed objectChurch_decodeAllProp
    (fun typed => objectChurch_decodeAllProp_admits typed)

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
