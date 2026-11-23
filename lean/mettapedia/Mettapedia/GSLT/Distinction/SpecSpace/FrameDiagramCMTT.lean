import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RegionalEquality
import Mettapedia.OSLF.MeTTaIL.ReflectiveQuoteAdmission
import Mettapedia.OSLF.MeTTaIL.ReflectiveContextualQuote

/-!
# Multi-Action Frame-Change Diagrams and Reflective Contextual Quote Views

This module develops multi-action frame-change geometry and connects it directly to
`Mettapedia.OSLF.MeTTaIL`'s live reflective quotation calculus (`Pattern`,
`ReflectiveQuoteAdmission`, `ReflectiveContextualQuote`):

1. **Multi-Action Frame-Change Diagrams (`FrameDiagram`)**:
   Lifts `RuleSyntax.RegionalEquality` (regional conversions over a single shared frame action)
   to arbitrary directed diagrams of *genuinely distinct* frame actions `(X_i : Frames Tm_i Hom_i)`
   connected by frame-change morphisms `FrameMap X_i X_j`, with 2-categorical compatible section
   semantics (`CompatibleSection`), faithful embedding of `RegionalEquality`, and concrete
   positive & negative cross-language controls (`ArithCore ⟶ SemNat`).
2. **Reflective Contextual Quote Views as Real `PackedFrames` & `FrameMap` (`ReflectiveViewFrames`)**:
   Instantiates `PackedFrames` directly on `Mettapedia.OSLF.MeTTaIL.Syntax.Pattern` modulo
   `ReflectiveCanonical.canonicalEquivalent declaration`, realizes `substituteUnder declaration
   scope depth replacement` for EVERY `QuoteScope` (`.closed`, `.reaching .apply`,
   `.reaching (.freeze _)`, `.reaching (.closure _)`) as an actual frame morphism
   (`CanonicalEndo`), constructs the real quotient `FrameMap` from strict syntactic `Pattern`
   frames to canonical reflective frames (`syntacticToCanonicalFrameMap`), proves syntactic vs.
   canonical separation on `@(*y)`, proves scope-agreement on sealed bodies, and bridges
   `ReflectiveQuoteAdmission` + `ReflectiveContextualQuote` directly (`ReflectiveBridge`).
3. **Lifting Step Admission and Runs Over Arbitrary Frame-Change Diagrams (`DiagramStep`)**:
   Pulls back `CompatibleSection` along natural frame morphisms, defines `DiagramStep` and
   multi-step `DiagramStep.Run`, proves `singletonDiagram_compatibleSection_iff_solvable`, and
   gives concrete 2-language firing positive & negative controls (`CrossLanguageStepControl`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.SpecSpace

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface (Frames)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax (RegionalEquality)

/-! ## Part 1: Multi-Action Frame-Change Diagrams -/

section FrameDiagrams

universe u uI

/-- A packed frame action bundling its frame-object type, term family, morphism family,
and `Frames` structure so distinct languages can coexist in a single diagram. -/
structure PackedFrames where
  Obj : Type u
  Tm : Obj → Type u
  Hom : Obj → Obj → Type u
  frames : Frames Tm Hom

/-- A **frame-change morphism** `Φ : F ⟶ G` between genuinely distinct frame actions:
maps frame objects, terms, and frame morphisms while preserving identity, composition,
substitution action, and frame equality `E`. -/
structure FrameMap (F G : PackedFrames.{u}) where
  onObj : F.Obj → G.Obj
  onTm : ∀ {a : F.Obj}, F.Tm a → G.Tm (onObj a)
  onHom : ∀ {a b : F.Obj}, F.Hom a b → G.Hom (onObj a) (onObj b)
  map_id : ∀ (a : F.Obj) (t : F.Tm a),
    G.frames.E (G.frames.act (onHom (F.frames.id a)) (onTm t)) (onTm t)
  map_comp : ∀ {a b c : F.Obj} (g : F.Hom b c) (f : F.Hom a b) (t : F.Tm a),
    G.frames.E
      (G.frames.act (onHom (F.frames.comp g f)) (onTm t))
      (G.frames.act (G.frames.comp (onHom g) (onHom f)) (onTm t))
  map_act : ∀ {a b : F.Obj} (σ : F.Hom a b) (t : F.Tm a),
    G.frames.E (onTm (F.frames.act σ t)) (G.frames.act (onHom σ) (onTm t))
  map_E : ∀ {a : F.Obj} {t u : F.Tm a},
    F.frames.E t u → G.frames.E (onTm t) (onTm u)

namespace FrameMap

/-- Identity frame-change morphism. -/
def id (F : PackedFrames.{u}) : FrameMap F F where
  onObj a := a
  onTm t := t
  onHom σ := σ
  map_id a t := by
    rw [F.frames.act_id]
    exact (F.frames.equivalence a).refl t
  map_comp g f t := (F.frames.equivalence _).refl _
  map_act σ t := (F.frames.equivalence _).refl _
  map_E h := h

/-- Composition of frame-change morphisms. -/
def comp {F G H : PackedFrames.{u}}
    (Ψ : FrameMap G H) (Φ : FrameMap F G) : FrameMap F H where
  onObj a := Ψ.onObj (Φ.onObj a)
  onTm t := Ψ.onTm (Φ.onTm t)
  onHom σ := Ψ.onHom (Φ.onHom σ)
  map_id a t := by
    have h1 := Ψ.map_E (Φ.map_id a t)
    have h2 := Ψ.map_act (Φ.onHom (F.frames.id a)) (Φ.onTm t)
    exact (H.frames.equivalence _).trans ((H.frames.equivalence _).symm h2) h1
  map_comp g f t := by
    have h1 := Ψ.map_E (Φ.map_comp g f t)
    have h2 := Ψ.map_act (Φ.onHom (F.frames.comp g f)) (Φ.onTm t)
    have h3 := Ψ.map_act (G.frames.comp (Φ.onHom g) (Φ.onHom f)) (Φ.onTm t)
    have h4 := Ψ.map_comp (Φ.onHom g) (Φ.onHom f) (Φ.onTm t)
    exact (H.frames.equivalence _).trans
      ((H.frames.equivalence _).symm h2)
      ((H.frames.equivalence _).trans h1 ((H.frames.equivalence _).trans h3 h4))
  map_act σ t := by
    have h1 := Ψ.map_E (Φ.map_act σ t)
    have h2 := Ψ.map_act (Φ.onHom σ) (Φ.onTm t)
    exact (H.frames.equivalence _).trans h1 h2
  map_E h := Ψ.map_E (Φ.map_E h)

/-- Transport an equation store along a frame-change morphism. -/
def mapStore {F G : PackedFrames.{u}} (Φ : FrameMap F G) {a : F.Obj}
    (store : EquationStore (F.Tm a)) : EquationStore (G.Tm (Φ.onObj a)) :=
  store.map fun e => (Φ.onTm e.1, Φ.onTm e.2)

/-- **Functoriality of equation modeling under frame change**:
if `σ` solves `store` in `F`, then `Φ.onHom σ` solves `Φ.mapStore store` in `G`. -/
theorem models_mapStore {F G : PackedFrames.{u}} (Φ : FrameMap F G)
    {a b : F.Obj} (σ : F.Hom a b) (store : EquationStore (F.Tm a))
    (hmod : F.frames.Models σ store) :
    G.frames.Models (Φ.onHom σ) (Φ.mapStore store) := by
  intro e he
  rcases List.mem_map.mp he with ⟨e₀, he₀, rfl⟩
  have hF : F.frames.E (F.frames.act σ e₀.1) (F.frames.act σ e₀.2) := hmod e₀ he₀
  have h1 := Φ.map_act σ e₀.1
  have h2 := Φ.map_E hF
  have h3 := Φ.map_act σ e₀.2
  exact (G.frames.equivalence _).trans
    ((G.frames.equivalence _).symm h1)
    ((G.frames.equivalence _).trans h2 h3)

/-- Corollary: frame-change morphisms preserve store solvability. -/
theorem solvable_mapStore {F G : PackedFrames.{u}} (Φ : FrameMap F G)
    {a : F.Obj} (store : EquationStore (F.Tm a))
    (hsol : F.frames.Solvable store) :
    G.frames.Solvable (Φ.mapStore store) := by
  obtain ⟨b, σ, hmod⟩ := hsol
  exact ⟨Φ.onObj b, Φ.onHom σ, Φ.models_mapStore σ store hmod⟩

end FrameMap

/-- A **multi-action frame-change diagram**: an indexed family of distinct frame actions
`node i` linked by directed frame-change morphisms `edgeMap`. -/
structure FrameDiagram (I : Type uI) where
  node : I → PackedFrames.{u}
  Edge : I → I → Type
  edgeMap : ∀ {i j : I}, Edge i j → FrameMap (node i) (node j)

/-- A **compatible section** (2-categorical lax cone of solutions) over a multi-action
frame-change diagram `D` with base frames `root` and local stores `stores`:
each node `i` has a solution `sol i` of `stores i`, and every directed edge
`e : D.Edge i j` carries a mediating morphism `coh e` reconciling the transported
source solution with the target solution up to target frame equality `E`. -/
structure CompatibleSection {I : Type uI} (D : FrameDiagram.{u, uI} I)
    (root : ∀ i : I, (D.node i).Obj)
    (stores : ∀ i : I, EquationStore ((D.node i).Tm (root i)))
    (edgeBase : ∀ {i j : I} (e : D.Edge i j),
      (D.node j).Hom ((D.edgeMap e).onObj (root i)) (root j)) where
  tgt : ∀ i : I, (D.node i).Obj
  sol : ∀ i : I, (D.node i).Hom (root i) (tgt i)
  models_node : ∀ i : I, (D.node i).frames.Models (sol i) (stores i)
  coh : ∀ {i j : I} (e : D.Edge i j),
    (D.node j).Hom ((D.edgeMap e).onObj (tgt i)) (tgt j)
  comm : ∀ {i j : I} (e : D.Edge i j) (t : (D.node i).Tm (root i)),
    (D.node j).frames.E
      ((D.node j).frames.act ((D.node j).frames.comp (sol j) (edgeBase e)) ((D.edgeMap e).onTm t))
      ((D.node j).frames.act ((D.node j).frames.comp (coh e) ((D.edgeMap e).onHom (sol i)))
        ((D.edgeMap e).onTm t))

/-- Along every edge `e : i ⟶ j` of a `CompatibleSection`, the target solution `sol j`
(pulled back along `edgeBase e`) automatically models the transported source store! -/
theorem CompatibleSection.models_transported_source {I : Type uI}
    {D : FrameDiagram.{u, uI} I}
    {root : ∀ i : I, (D.node i).Obj}
    {stores : ∀ i : I, EquationStore ((D.node i).Tm (root i))}
    {edgeBase : ∀ {i j : I} (e : D.Edge i j),
      (D.node j).Hom ((D.edgeMap e).onObj (root i)) (root j)}
    (sec : CompatibleSection D root stores edgeBase)
    {i j : I} (e : D.Edge i j) :
    (D.node j).frames.Models ((D.node j).frames.comp (sec.sol j) (edgeBase e))
      ((D.edgeMap e).mapStore (stores i)) := by
  intro eq heq
  rcases List.mem_map.mp heq with ⟨eq₀, heq₀, rfl⟩
  have h1 := sec.comm e eq₀.1
  have h2 := sec.comm e eq₀.2
  have hsrc : (D.node j).frames.Models ((D.edgeMap e).onHom (sec.sol i))
      ((D.edgeMap e).mapStore (stores i)) :=
    (D.edgeMap e).models_mapStore (sec.sol i) (stores i) (sec.models_node i)
  have hmid0 : (D.node j).frames.E
      ((D.node j).frames.act ((D.edgeMap e).onHom (sec.sol i)) ((D.edgeMap e).onTm eq₀.1))
      ((D.node j).frames.act ((D.edgeMap e).onHom (sec.sol i)) ((D.edgeMap e).onTm eq₀.2)) :=
    hsrc ((D.edgeMap e).onTm eq₀.1, (D.edgeMap e).onTm eq₀.2)
      (List.mem_map.mpr ⟨eq₀, heq₀, rfl⟩)
  have hmid1 := (D.node j).frames.preserves (sec.coh e) hmid0
  rw [← (D.node j).frames.act_comp, ← (D.node j).frames.act_comp] at hmid1
  exact (D.node j).frames.equivalence _ |>.trans h1
    ((D.node j).frames.equivalence _ |>.trans hmid1
      ((D.node j).frames.equivalence _ |>.symm h2))

/-- **Faithful embedding of `RuleSyntax.RegionalEquality` into `FrameDiagram`**:
every single-action `RegionalEquality base Region` produces a `FrameDiagram` whose node
at `r : Region` carries the regional conversion frame `r`, linked by identity-carrier
refinement edges `∀ {a} t u, conv r₁ t u → conv r₂ t u`. -/
abbrev regionPackedFrame {Obj : Type u} {Tm : Obj → Type u} {Hom : Obj → Obj → Type u}
    {Region : Type uI} {base : Frames Tm Hom}
    (views : RegionalEquality base Region) (r : Region) : PackedFrames.{u} where
  Obj := Obj
  Tm := Tm
  Hom := Hom
  frames :=
    { E := fun {a} t u => (views.conversion r a).r t u
      equivalence := fun a => (views.conversion r a).iseqv
      act := base.act
      id := base.id
      comp := base.comp
      act_id := base.act_id
      act_comp := base.act_comp
      preserves := fun {_ _} σ {_ _} h => views.preserves r σ h }

/-- Frame diagram generated by a `RegionalEquality`: edges are conversion coarsenings. -/
abbrev diagramOfRegionalEquality {Obj : Type u} {Tm : Obj → Type u} {Hom : Obj → Obj → Type u}
    {Region : Type uI} {base : Frames Tm Hom}
    (views : RegionalEquality base Region) : FrameDiagram.{u, uI} Region where
  node r := regionPackedFrame views r
  Edge r₁ r₂ := PLift (∀ {a : Obj} {t u : Tm a}, (views.conversion r₁ a).r t u →
    (views.conversion r₂ a).r t u)
  edgeMap {r₁ r₂} h :=
    { onObj := fun a => a
      onTm := fun t => t
      onHom := fun σ => σ
      map_id := fun a t => by
        rw [base.act_id]
      map_comp := fun g f t => (views.conversion r₂ _).iseqv.refl _
      map_act := fun σ t => (views.conversion r₂ _).iseqv.refl _
      map_E := fun he => h.down he }

/-- **Faithfulness Theorem**: a single shared assignment `σ` models a mixed regional store
in `views.frames` if and only if it yields a `CompatibleSection` (with constant target `b`
and solution `σ`) of `diagramOfRegionalEquality views` over the per-region projections. -/
theorem regionalEquality_models_of_common_section
    {Obj : Type u} {Tm : Obj → Type u} {Hom : Obj → Obj → Type u}
    {Region : Type uI} [DecidableEq Region] {base : Frames Tm Hom}
    (views : RegionalEquality base Region)
    {a b : Obj} (σ : Hom a b)
    (store : EquationStore (Region × Tm a))
    (hregion : ∀ e ∈ store, e.1.1 = e.2.1) :
    views.frames.Models σ store ↔
      (∀ r : Region,
        ((diagramOfRegionalEquality views).node r).frames.Models σ
          ((store.filter fun e => decide (e.1.1 = r)).map fun e => (e.1.2, e.2.2))) := by
  rw [views.models_iff]
  constructor
  · intro hmod r eq heq
    rcases List.mem_map.mp heq with ⟨e, he, rfl⟩
    have hfilt := List.mem_filter.mp he
    have hr : e.1.1 = r := of_decide_eq_true hfilt.2
    have hm := (hmod e hfilt.1).2
    rwa [hr] at hm
  · intro hsec e he
    have hr := hregion e he
    refine ⟨hr, ?_⟩
    have hmem : (e.1.2, e.2.2) ∈
        (store.filter fun x => decide (x.1.1 = e.1.1)).map fun x => (x.1.2, x.2.2) :=
      List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, decide_eq_true rfl⟩, rfl⟩
    exact hsec e.1.1 (e.1.2, e.2.2) hmem

/-! ### Concrete 2-Language Multi-Action Diagram Controls (`ArithCore ⟶ SemNat`) -/

namespace CrossLanguageControl

/-- Strict syntactic arithmetic terms with a single unknown `x`. -/
inductive ArithTm where
  | zero : ArithTm
  | succ : ArithTm → ArithTm
  | var : ArithTm
  | add : ArithTm → ArithTm → ArithTm
  deriving DecidableEq, Repr

/-- AST node count used to prove strict syntactic non-circularity. -/
def ArithTm.size : ArithTm → ℕ
  | .zero => 1
  | .succ t => t.size + 1
  | .var => 1
  | .add t u => t.size + u.size + 1

/-- Substitution of `x ↦ v` in `ArithTm`. -/
def substArith (v : ArithTm) : ArithTm → ArithTm
  | .zero => .zero
  | .succ t => .succ (substArith v t)
  | .var => v
  | .add t u => .add (substArith v t) (substArith v u)

/-- Strict syntactic frame action (`E := Eq`). -/
abbrev arithPacked : PackedFrames.{0} where
  Obj := PUnit
  Tm _ := ArithTm
  Hom _ _ := ArithTm
  frames :=
    { E := Eq
      equivalence := fun _ => eq_equivalence
      act := substArith
      id := fun _ => .var
      comp := fun g f => substArith g f
      act_id := fun t => by
        induction t with
        | zero => rfl
        | succ _ ih => exact congrArg ArithTm.succ ih
        | var => rfl
        | add _ _ ih1 ih2 => exact congrArg₂ ArithTm.add ih1 ih2
      act_comp := fun g f t => by
        induction t with
        | zero => rfl
        | succ _ ih => exact congrArg ArithTm.succ ih
        | var => rfl
        | add _ _ ih1 ih2 => exact congrArg₂ ArithTm.add ih1 ih2
      preserves := fun {_ _} σ {_ _} h => congrArg (substArith σ) h }

/-- Semantic affine-Nat terms (`a * x + b`, representing exact linear polynomials over `ℕ`). -/
structure AffineNat where
  coeff : ℕ
  const : ℕ
  deriving DecidableEq, Repr

/-- Composition of affine maps `(c2 * (c1 * x + k1) + k2)`. -/
def substAffine (v : AffineNat) (t : AffineNat) : AffineNat :=
  ⟨t.coeff * v.coeff, t.coeff * v.const + t.const⟩

/-- Semantic arithmetic frame action (`E := Eq` on normalized affine polynomials). -/
abbrev semNatPacked : PackedFrames.{0} where
  Obj := PUnit
  Tm _ := AffineNat
  Hom _ _ := AffineNat
  frames :=
    { E := Eq
      equivalence := fun _ => eq_equivalence
      act := substAffine
      id := fun _ => ⟨1, 0⟩
      comp := fun g f => substAffine g f
      act_id := fun ⟨c, k⟩ => by
        simp [substAffine]
      act_comp := fun ⟨cg, kg⟩ ⟨cf, kf⟩ ⟨ct, kt⟩ => by
        simp only [substAffine]
        congr 1
        · exact (Nat.mul_assoc ct cf cg).symm
        · rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
      preserves := fun {_ _} σ {_ _} h => congrArg (substAffine σ) h }

/-- Compile syntactic `ArithTm` into normalized `AffineNat`. -/
def evalArith : ArithTm → AffineNat
  | .zero => ⟨0, 0⟩
  | .succ t => ⟨(evalArith t).coeff, (evalArith t).const + 1⟩
  | .var => ⟨1, 0⟩
  | .add t u => ⟨(evalArith t).coeff + (evalArith u).coeff, (evalArith t).const + (evalArith u).const⟩

theorem evalArith_subst (σ t : ArithTm) :
    evalArith (substArith σ t) = substAffine (evalArith σ) (evalArith t) := by
  induction t with
  | zero => simp [substArith, evalArith, substAffine]
  | succ t ih =>
      simp only [substArith, evalArith, ih, substAffine, Nat.add_assoc]
  | var =>
      simp [substArith, evalArith, substAffine]
  | add t u ih1 ih2 =>
      simp only [substArith, evalArith, ih1, ih2, substAffine]
      congr 1
      · exact (Nat.add_mul _ _ _).symm
      · rw [Nat.add_mul]
        omega

/-- Non-injective frame-change morphism `arithPacked ⟶ semNatPacked`. -/
def evalFrameMap : FrameMap arithPacked semNatPacked where
  onObj _ := PUnit.unit
  onTm t := evalArith t
  onHom σ := evalArith σ
  map_id _ t := by
    change substAffine ⟨1, 0⟩ (evalArith t) = evalArith t
    cases evalArith t with
    | mk c k => simp [substAffine]
  map_comp g f t := by
    change substAffine (evalArith (substArith g f)) (evalArith t) =
      substAffine (substAffine (evalArith g) (evalArith f)) (evalArith t)
    rw [evalArith_subst]
  map_act σ t := evalArith_subst σ t
  map_E h := congrArg evalArith h

/-- Inductive edge type for the two-language diagram (`false ⟶ true`), eliminating
dependent equality transport so pattern matching reduces definitionally. -/
inductive TwoEdge : Bool → Bool → Type where
  | eval : TwoEdge false true

/-- Two-language diagram with node `false = arithPacked`, node `true = semNatPacked`,
and a single directed frame-change edge `.eval : TwoEdge false true`. -/
abbrev twoLangDiagram : FrameDiagram.{0, 0} Bool where
  node b := if b then semNatPacked else arithPacked
  Edge := TwoEdge
  edgeMap := fun {_ _} e => match e with | .eval => evalFrameMap

/-- **Positive Multi-Action Control**:
The cross-language store requiring `x = succ zero` in `arithPacked` and
`eval(add zero x) = eval(succ zero)` in `semNatPacked` admits a genuine `CompatibleSection`,
even though `add zero x` is NOT syntactically equal to `x` in `arithPacked`. -/
theorem crossLang_positive_section :
    Nonempty (CompatibleSection twoLangDiagram
      (fun b => match b with | false => PUnit.unit | true => PUnit.unit)
      (fun b => match b with
        | false => [(.var, .succ .zero)]
        | true => [(evalArith (.add .zero .var), evalArith (.succ .zero))])
      (fun {_ _} e => match e with | .eval => ⟨1, 0⟩)) := by
  refine ⟨⟨fun b => match b with | false => PUnit.unit | true => PUnit.unit,
    fun b => match b with
      | false => .succ .zero
      | true => ⟨0, 1⟩,
    ?_,
    fun {_ _} e => match e with | .eval => ⟨1, 0⟩,
    ?_⟩⟩
  · intro b
    cases b with
    | false =>
        intro eq heq
        rcases List.mem_singleton.mp heq with rfl
        rfl
    | true =>
        intro eq heq
        rcases List.mem_singleton.mp heq with rfl
        rfl
  · intro i j e t
    cases e
    change substAffine (substAffine ⟨0, 1⟩ ⟨1, 0⟩) (evalArith t) =
      substAffine (substAffine ⟨1, 0⟩ (evalArith (.succ .zero))) (evalArith t)
    rfl

/-- **Negative Multi-Action Control**:
1. Inside strict `arithPacked`, `add zero var = var` has NO solution (syntactic rigidity).
2. Across `twoLangDiagram`, conflicting assignments `var = zero` in `arithPacked` and
   `eval(var) = succ zero` in `semNatPacked` admit NO `CompatibleSection`! -/
theorem crossLang_negative_controls :
    (¬ arithPacked.frames.Solvable (a := PUnit.unit) [(.add .zero .var, .var)]) ∧
    (IsEmpty (CompatibleSection twoLangDiagram
      (fun b => match b with | false => PUnit.unit | true => PUnit.unit)
      (fun b => match b with
        | false => [(.var, .zero)]
        | true => [(evalArith .var, evalArith (.succ .zero))])
      (fun {_ _} e => match e with | .eval => ⟨1, 0⟩))) := by
  constructor
  · rintro ⟨_, σ, hmod⟩
    have heq := hmod (.add .zero .var, .var) (List.mem_singleton_self _)
    change ArithTm.add .zero σ = σ at heq
    have hsz := congrArg ArithTm.size heq
    simp only [ArithTm.size] at hsz
    omega
  · refine ⟨fun sec => ?_⟩
    have h0 : sec.sol false = .zero := by
      have hm := sec.models_node false (.var, .zero) (List.mem_singleton_self _)
      exact hm
    have h1 : substAffine (sec.sol true) ⟨1, 0⟩ = ⟨0, 1⟩ := by
      have hm := sec.models_node true (evalArith .var, evalArith (.succ .zero))
        (List.mem_singleton_self _)
      change substAffine (sec.sol true) ⟨1, 0⟩ = substAffine (sec.sol true) ⟨0, 1⟩ at hm
      simpa [substAffine] using hm
    have hcomm := sec.comm (i := false) (j := true) .eval .var
    change substAffine (substAffine (sec.sol true) ⟨1, 0⟩) ⟨1, 0⟩ =
      substAffine (substAffine (sec.coh .eval) (evalArith (sec.sol false))) ⟨1, 0⟩ at hcomm
    rw [h0] at hcomm
    have hL : substAffine (substAffine (sec.sol true) ⟨1, 0⟩) ⟨1, 0⟩ = ⟨0, 1⟩ := by
      rw [h1]; rfl
    have hR : substAffine (substAffine (sec.coh .eval) (evalArith .zero)) ⟨1, 0⟩ = ⟨0, 0⟩ := by
      cases sec.coh .eval with
      | mk c k => simp [evalArith, substAffine]
    rw [hL, hR] at hcomm
    cases hcomm

end CrossLanguageControl

end FrameDiagrams


/-! ## Part 2: Reflective Contextual Quote Views as Real `PackedFrames` & `FrameMap` -/

namespace ReflectiveViewFrames

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ReflectiveQuoteAdmission
open Mettapedia.OSLF.MeTTaIL.ReflectiveContextualQuote

/-- An endomorphism of `Pattern` that respects `canonicalEquivalent declaration`. -/
structure CanonicalEndo (declaration : ReflectivePresentationDecl) where
  fn : Pattern → Pattern
  respects : ∀ {a b : Pattern},
    canonicalEquivalent declaration a b = true →
    canonicalEquivalent declaration (fn a) (fn b) = true

namespace CanonicalEndo

def id (declaration : ReflectivePresentationDecl) : CanonicalEndo declaration where
  fn := _root_.id
  respects h := h

def comp {declaration : ReflectivePresentationDecl}
    (g f : CanonicalEndo declaration) : CanonicalEndo declaration where
  fn t := g.fn (f.fn t)
  respects h := g.respects (f.respects h)

end CanonicalEndo

/-- `canonicalEquivalent declaration · · = true` is an equivalence relation on `Pattern`. -/
theorem canonicalEquivalent_equivalence (declaration : ReflectivePresentationDecl) :
    Equivalence (fun a b : Pattern => canonicalEquivalent declaration a b = true) where
  refl _ := canonicalEquivalent_eq_true_iff.mpr rfl
  symm hab := canonicalEquivalent_eq_true_iff.mpr (canonicalEquivalent_eq_true_iff.mp hab).symm
  trans hab hbc := canonicalEquivalent_eq_true_iff.mpr
    ((canonicalEquivalent_eq_true_iff.mp hab).trans (canonicalEquivalent_eq_true_iff.mp hbc))

/-- **Real `PackedFrames` on `Pattern` modulo `canonicalEquivalent declaration`**,
whose frame morphisms are `CanonicalEndo declaration` (including `substituteUnder` for every
`QuoteScope`). -/
def reflectiveCanonicalFrames (declaration : ReflectivePresentationDecl) : PackedFrames.{0} where
  Obj := Unit
  Tm _ := Pattern
  Hom _ _ := CanonicalEndo declaration
  frames :=
    { E := fun a b => canonicalEquivalent declaration a b = true
      equivalence := fun _ => canonicalEquivalent_equivalence declaration
      act := fun σ t => σ.fn t
      id := fun _ => CanonicalEndo.id declaration
      comp := fun g f => CanonicalEndo.comp g f
      act_id := fun _ => rfl
      act_comp := fun _ _ _ => rfl
      preserves := fun σ _ _ h => σ.respects h }

/-- **Strict syntactic `PackedFrames` on `Pattern`** (equality `Eq`, same endomorphism supply
`CanonicalEndo declaration`). -/
def syntacticPatternFrames (declaration : ReflectivePresentationDecl) : PackedFrames.{0} where
  Obj := Unit
  Tm _ := Pattern
  Hom _ _ := CanonicalEndo declaration
  frames :=
    { E := Eq
      equivalence := fun _ => eq_equivalence
      act := fun σ t => σ.fn t
      id := fun _ => CanonicalEndo.id declaration
      comp := fun g f => CanonicalEndo.comp g f
      act_id := fun _ => rfl
      act_comp := fun _ _ _ => rfl
      preserves := fun σ _ _ h => congrArg σ.fn h }

/-- **Real Quotient `FrameMap`**: maps strict syntactic `Pattern` frames to canonical reflective
`Pattern` frames (`canonicalEquivalent`). -/
def syntacticToCanonicalFrameMap (declaration : ReflectivePresentationDecl) :
    FrameMap (syntacticPatternFrames declaration) (reflectiveCanonicalFrames declaration) where
  onObj a := a
  onTm t := t
  onHom σ := σ
  map_id _ t := (canonicalEquivalent_equivalence declaration).refl t
  map_comp _ _ t := (canonicalEquivalent_equivalence declaration).refl _
  map_act _ t := (canonicalEquivalent_equivalence declaration).refl _
  map_E h := by
    subst h
    exact (canonicalEquivalent_equivalence declaration).refl _

/-- **Every `QuoteScope` binder elimination (`substituteUnder`) is a real frame morphism**
in `reflectiveCanonicalFrames declaration`. -/
def substituteUnderHom (declaration : ReflectivePresentationDecl)
    (scope : QuoteScope) (depth : Nat) (replacement : Pattern) :
    CanonicalEndo declaration where
  fn := substituteUnder declaration scope depth replacement
  respects h := substituteUnder_respects scope depth replacement h

/-- **Real Syntactic vs. Canonical Frame Separation on `@(*#0)`**:
In `rhoReflectivePresentation`, `@(*#0)` (`NQuote (PDrop (bvar 0))`) and `#0` (`bvar 0`) are:
1. strictly distinct in `syntacticPatternFrames`, yet
2. equivalent in `reflectiveCanonicalFrames` (so `syntacticToCanonicalFrameMap` merges them!). -/
theorem rho_quote_drop_separates_syntactic_from_canonical_frames :
    let decl := rhoReflectivePresentation.toReflectivePresentationDecl
    let lhs : Pattern := .apply "NQuote" [.apply "PDrop" [.bvar 0]]
    let rhs : Pattern := .bvar 0
    ¬ (syntacticPatternFrames decl).frames.E (a := ()) lhs rhs ∧
    (reflectiveCanonicalFrames decl).frames.E (a := ())
      ((syntacticToCanonicalFrameMap decl).onTm (a := ()) lhs)
      ((syntacticToCanonicalFrameMap decl).onTm (a := ()) rhs) := by
  refine ⟨?_, ?_⟩
  · intro h
    cases h
  · change canonicalEquivalent rhoReflectivePresentation.toReflectivePresentationDecl
      (.apply "NQuote" [.apply "PDrop" [.bvar 0]]) (.bvar 0) = true
    decide +kernel

/-- **Scope-Coherence on Sealed Bodies**:
For any two quote scopes `s₁ s₂ : QuoteScope`, if `body` is admitted under `.closed`
(sealed) and well-scoped at `depth + 1`, then `substituteUnderHom` yields the exact same
result under `s₁` and `s₂`. -/
theorem substituteUnderHom_agrees_across_scopes_on_sealed
    (declaration : ReflectivePresentationDecl) (s₁ s₂ : QuoteScope)
    {depth : Nat} {replacement body : Pattern}
    (admitted : scopeAdmits declaration .closed depth body = true)
    (inScope : body.isWellScopedAt (depth + 1) = true) :
    (substituteUnderHom declaration s₁ depth replacement).fn body =
    (substituteUnderHom declaration s₂ depth replacement).fn body := by
  change substituteUnder declaration s₁ depth replacement body =
    substituteUnder declaration s₂ depth replacement body
  rw [substituteUnder_eq_instantiate_of_sealed s₁ admitted inScope,
      substituteUnder_eq_instantiate_of_sealed s₂ admitted inScope]

/-- **Scope-Safety & Equation-Respect Bundle for `substituteUnder`**:
Every `QuoteScope` preserves both `canonicalEquivalent` (`substituteUnder_respects`) and
de Bruijn well-scopedness on admitted/scope-safe bodies (`substituteUnder_scoped`,
`substituteUnder_scoped_of_scopeSafeAt`). -/
theorem substituteUnder_frame_laws (declaration : ReflectivePresentationDecl)
    (scope : QuoteScope) (depth : Nat) (replacement : Pattern) :
    (∀ {left right : Pattern},
      canonicalEquivalent declaration left right = true →
      canonicalEquivalent declaration
        ((substituteUnderHom declaration scope depth replacement).fn left)
        ((substituteUnderHom declaration scope depth replacement).fn right) = true) ∧
    (∀ {body : Pattern},
      scopeAdmits declaration scope depth body = true →
      body.isWellScopedAt (depth + 1) = true →
      replacement.isWellScopedAt 0 = true →
      ((substituteUnderHom declaration scope depth replacement).fn body).isWellScopedAt depth = true) :=
  ⟨fun h => substituteUnder_respects scope depth replacement h,
   fun hadm hbody hrep => substituteUnder_scoped scope hadm hbody hrep⟩

/-- **Reflective Sorting–Admission Separation and Closure-View Factorization Bridge**:
Connects `Mettapedia.OSLF.MeTTaIL.ReflectiveQuoteAdmission` and
`Mettapedia.OSLF.MeTTaIL.ReflectiveContextualQuote` cleanly with zero synthetic proxies:
1. Structural sorting (`NameWellSorted`, `ProcWellSorted`) is invariant under changing the
   quote-scope policy (`nameWellSorted_withQuoteScope_iff`, `procWellSorted_withQuoteScope_iff`).
2. Quote admission (`quoteAdmits`) depends on the quote-scope policy (`quoteAdmits_reads_quoteScope`),
   separating `@(y!(0))` (`sorted_not_admitted`) from `@(*y)` (`admitted_not_sealed`).
3. For every reflective presentation, depth, replacement, and body, there exists a fresh
   context constructor whose `closureView` simultaneously factors `applyView` via `erase`
   and `freezeView` via `atomize` (`exists_closure_factorization`).
4. Without freshness, NO observer on `closureView` recovers `applyView` or `freezeView` across
   all bodies (`closureView_not_factorable`, `closureView_not_factorable_freeze`), matching the
   validator (`closure_fresh_context_validates`, `closure_signature_context_rejected`). -/
theorem reflective_sorting_admission_and_closure_bridge :
    (∀ (presentation : ReflectiveProcessSignature) (free : FreeSortContext)
        (scope : QuoteScope) (bound : List String) (name : Pattern),
      NameWellSorted (presentation.withQuoteScope scope) free bound name ↔
        NameWellSorted presentation free bound name) ∧
    (∀ (presentation : ReflectiveProcessSignature) (free : FreeSortContext)
        (scope : QuoteScope) (bound : List String) (process : Pattern),
      ProcWellSorted (presentation.withQuoteScope scope) free bound process ↔
        ProcWellSorted presentation free bound process) ∧
    (quoteAdmits (rhoReflectivePresentation.withQuoteScope .closed).toReflectivePresentationDecl
        (.apply "POutput" [.bvar 0, .apply "PZero" []]) = false ∧
      quoteAdmits (rhoReflectivePresentation.withQuoteScope (.reaching .apply)).toReflectivePresentationDecl
        (.apply "POutput" [.bvar 0, .apply "PZero" []]) = true) ∧
    (∀ (declaration : ReflectivePresentationDecl) (depth : Nat) (replacement body : Pattern),
      ∃ context,
        erase declaration context (closureView declaration context depth replacement body) =
            applyView declaration depth replacement body ∧
          ∀ name : Pattern, name.isWellScopedAt 0 = true →
            atomize declaration context name
              (closureView declaration context depth replacement body) =
            freezeView declaration depth replacement name body) ∧
    (∃ (decl : ReflectivePresentationDecl) (ctx : String) (rep : Pattern),
      ¬ ∃ observe : Pattern → Pattern, ∀ body,
        observe (closureView decl ctx 0 rep body) = applyView decl 0 rep body) ∧
    (rhoCalc.validateReflectivePresentation
      { rhoReflectivePresentation.toReflectivePresentationDecl with
        quoteScope := .reaching (.closure "QuoteContext") } = [] ∧
     (rhoCalc.validateReflectivePresentation
      { rhoReflectivePresentation.toReflectivePresentationDecl with
        quoteScope := .reaching (.closure "PZero") }).length = 1) :=
  ⟨fun _ _ scope _ _ => nameWellSorted_withQuoteScope_iff scope,
   fun _ _ scope _ _ => procWellSorted_withQuoteScope_iff scope,
   quoteAdmits_reads_quoteScope,
   exists_closure_factorization,
   ⟨_, _, _, closureView_not_factorable⟩,
   ⟨closure_fresh_context_validates, closure_signature_context_rejected⟩⟩

end ReflectiveViewFrames

/-! ## Part 3: Lifting Step Admission and Runs Over Arbitrary Frame-Change Diagrams -/

section DiagramSteps

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uD uDI uOcc uS uF

/-- **Pullback of a `CompatibleSection` along a natural family of frame morphisms**
`φ : ∀ i, Hom (root₁ i) (root₂ i)` that commute with the diagram's base edge arrows
and refine each node's equation store. -/
def CompatibleSection.pullback {I : Type uDI} {D : FrameDiagram.{uD, uDI} I}
    {root₁ root₂ : ∀ i : I, (D.node i).Obj}
    {stores₁ : ∀ i : I, EquationStore ((D.node i).Tm (root₁ i))}
    {stores₂ : ∀ i : I, EquationStore ((D.node i).Tm (root₂ i))}
    {edgeBase₁ : ∀ {i j : I} (e : D.Edge i j),
      (D.node j).Hom ((D.edgeMap e).onObj (root₁ i)) (root₁ j)}
    {edgeBase₂ : ∀ {i j : I} (e : D.Edge i j),
      (D.node j).Hom ((D.edgeMap e).onObj (root₂ i)) (root₂ j)}
    (φ : ∀ i : I, (D.node i).Hom (root₁ i) (root₂ i))
    (sec : CompatibleSection D root₂ stores₂ edgeBase₂)
    (hrefine : ∀ i : I,
      (D.node i).frames.Models ((D.node i).frames.comp (sec.sol i) (φ i)) (stores₁ i))
    (hsquare : ∀ {i j : I} (e : D.Edge i j) (t : (D.node i).Tm (root₁ i)),
      (D.node j).frames.E
        ((D.node j).frames.act ((D.node j).frames.comp (φ j) (edgeBase₁ e)) ((D.edgeMap e).onTm t))
        ((D.node j).frames.act ((D.node j).frames.comp (edgeBase₂ e) ((D.edgeMap e).onHom (φ i)))
          ((D.edgeMap e).onTm t))) :
    CompatibleSection D root₁ stores₁ edgeBase₁ where
  tgt := sec.tgt
  sol i := (D.node i).frames.comp (sec.sol i) (φ i)
  models_node := hrefine
  coh e := sec.coh e
  comm {i j} e t := by
    let Xj := (D.node j).frames
    let eqv := Xj.equivalence (sec.tgt j)
    let Φ := D.edgeMap e
    have hL1 : Xj.E
        (Xj.act (Xj.comp (Xj.comp (sec.sol j) (φ j)) (edgeBase₁ e)) (Φ.onTm t))
        (Xj.act (sec.sol j) (Xj.act (Xj.comp (φ j) (edgeBase₁ e)) (Φ.onTm t))) := by
      rw [Xj.act_comp, Xj.act_comp, Xj.act_comp]
      exact eqv.refl _
    have hSq := Xj.preserves (sec.sol j) (hsquare e t)
    have hMid : Xj.E
        (Xj.act (sec.sol j) (Xj.act (Xj.comp (edgeBase₂ e) (Φ.onHom (φ i))) (Φ.onTm t)))
        (Xj.act (Xj.comp (sec.sol j) (edgeBase₂ e)) (Φ.onTm ((D.node i).frames.act (φ i) t))) := by
      have hact := Φ.map_act (φ i) t
      have hact' := Xj.preserves (Xj.comp (sec.sol j) (edgeBase₂ e)) hact
      rw [Xj.act_comp, Xj.act_comp]
      exact eqv.symm (by simpa only [Xj.act_comp] using hact')
    have hSec := sec.comm e ((D.node i).frames.act (φ i) t)
    have hR1 : Xj.E
        (Xj.act (Xj.comp (sec.coh e) (Φ.onHom (sec.sol i))) (Φ.onTm ((D.node i).frames.act (φ i) t)))
        (Xj.act (Xj.comp (sec.coh e) (Φ.onHom ((D.node i).frames.comp (sec.sol i) (φ i)))) (Φ.onTm t)) := by
      have hact := Φ.map_act (φ i) t
      have hcomp := Φ.map_comp (sec.sol i) (φ i) t
      have h1 := Xj.preserves (Xj.comp (sec.coh e) (Φ.onHom (sec.sol i))) hact
      have h2 := Xj.preserves (sec.coh e) ((Xj.equivalence _).symm hcomp)
      have h1' : Xj.E
          (Xj.act (Xj.comp (sec.coh e) (Φ.onHom (sec.sol i))) (Φ.onTm ((D.node i).frames.act (φ i) t)))
          (Xj.act (sec.coh e) (Xj.act (Xj.comp (Φ.onHom (sec.sol i)) (Φ.onHom (φ i))) (Φ.onTm t))) := by
        simpa only [Xj.act_comp] using h1
      have h2' : Xj.E
          (Xj.act (sec.coh e) (Xj.act (Xj.comp (Φ.onHom (sec.sol i)) (Φ.onHom (φ i))) (Φ.onTm t)))
          (Xj.act (Xj.comp (sec.coh e) (Φ.onHom ((D.node i).frames.comp (sec.sol i) (φ i)))) (Φ.onTm t)) := by
        rw [Xj.act_comp (sec.coh e) (Φ.onHom ((D.node i).frames.comp (sec.sol i) (φ i)))]
        exact h2
      exact eqv.trans h1' h2'
    exact eqv.trans hL1 (eqv.trans hSq (eqv.trans hMid (eqv.trans hSec hR1)))

/-- **Multi-Action Diagram Step System** lifting `Interface.Step` over an arbitrary
heterogeneous `FrameDiagram D`:
each state carries per-node frames, occurrence sets, local knowledge stores, and
cross-node base frame arrows; an admitted firing requires shapes, per-node occurrence
commit enabledness, a global `CompatibleSection` of the extended multi-action information
stores, and universal guard entailment over ALL compatible sections! -/
structure DiagramStep {I : Type uDI} (D : FrameDiagram.{uD, uDI} I)
    (O : Type uOcc) [DecidableEq O] (State : Type uS) (Firing : State → Type uF) where
  frame : State → ∀ i : I, (D.node i).Obj
  present : State → I → Finset O
  knowledge : (s : State) → ∀ i : I, EquationStore ((D.node i).Tm (frame s i))
  edgeBase : (s : State) → ∀ {i j : I} (e : D.Edge i j),
    (D.node j).Hom ((D.edgeMap e).onObj (frame s i)) (frame s j)
  target : {s : State} → Firing s → ∀ i : I, (D.node i).Obj
  extension : {s : State} → (f : Firing s) → ∀ i : I,
    (D.node i).Hom (frame s i) (target f i)
  targetEdgeBase : {s : State} → (f : Firing s) → ∀ {i j : I} (e : D.Edge i j),
    (D.node j).Hom ((D.edgeMap e).onObj (target f i)) (target f j)
  selection : {s : State} → Firing s → I → Selection O
  information : {s : State} → (f : Firing s) → ∀ i : I,
    EquationStore ((D.node i).Tm (target f i))
  Shapes : {s : State} → Firing s → Prop
  Holds : {s : State} → (f : Firing s) →
    CompatibleSection D (target f) (information f) (targetEdgeBase f) → Prop
  ext_square : ∀ {s : State} (f : Firing s) {i j : I} (e : D.Edge i j)
      (t : (D.node i).Tm (frame s i)),
    (D.node j).frames.E
      ((D.node j).frames.act ((D.node j).frames.comp (extension f j) (edgeBase s e))
        ((D.edgeMap e).onTm t))
      ((D.node j).frames.act ((D.node j).frames.comp (targetEdgeBase f e)
          ((D.edgeMap e).onHom (extension f i)))
        ((D.edgeMap e).onTm t))
  information_refines : ∀ {s : State} (f : Firing s)
      (sec : CompatibleSection D (target f) (information f) (targetEdgeBase f)) (i : I),
    (D.node i).frames.Models
      ((D.node i).frames.comp (sec.sol i) (extension f i)) (knowledge s i)
  preparedResult : {s : State} → (f : Firing s) →
    (Shapes f ∧
      (∀ i : I, Enabled (fun _ : O => ()) (present s i) ((selection f i).commit (T := Unit))) ∧
      Nonempty (CompatibleSection D (target f) (information f) (targetEdgeBase f))) → State
  preparedSettle : {s : State} → (f : Firing s) →
    (p : Shapes f ∧
      (∀ i : I, Enabled (fun _ : O => ()) (present s i) ((selection f i).commit (T := Unit))) ∧
      Nonempty (CompatibleSection D (target f) (information f) (targetEdgeBase f))) →
    ∀ i : I, (D.node i).Hom (target f i) (frame (preparedResult f p) i)
  present_preparedResult : ∀ {s : State} (f : Firing s) (p) (i : I),
    present (preparedResult f p) i = fire (present s i) ((selection f i).commit (T := Unit))
  settle_square : ∀ {s : State} (f : Firing s) (p) {i j : I} (e : D.Edge i j)
      (t : (D.node i).Tm (target f i)),
    (D.node j).frames.E
      ((D.node j).frames.act ((D.node j).frames.comp (preparedSettle f p j) (targetEdgeBase f e))
        ((D.edgeMap e).onTm t))
      ((D.node j).frames.act ((D.node j).frames.comp (edgeBase (preparedResult f p) e)
          ((D.edgeMap e).onHom (preparedSettle f p i)))
        ((D.edgeMap e).onTm t))
  result_refines : ∀ {s : State} (f : Firing s) (p)
      (sec : CompatibleSection D (frame (preparedResult f p))
        (knowledge (preparedResult f p)) (edgeBase (preparedResult f p))) (i : I),
    (D.node i).frames.Models
      ((D.node i).frames.comp (sec.sol i) (preparedSettle f p i)) (information f i)

namespace DiagramStep

variable {I : Type uDI} {D : FrameDiagram.{uD, uDI} I}
  {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : DiagramStep D O State Firing)

/-- Preparation of a multi-action diagram firing: shapes, per-node commit enabledness,
and existence of a global compatible section across the diagram. -/
abbrev Prepares {s : State} (f : Firing s) : Prop :=
  P.Shapes f ∧
  (∀ i : I, Enabled (fun _ : O => ()) (P.present s i) ((P.selection f i).commit (T := Unit))) ∧
  Nonempty (CompatibleSection D (P.target f) (P.information f) (P.targetEdgeBase f))

/-- Admission of a multi-action diagram firing: prepared AND every compatible section
of the extended multi-action information store entails the firing's guards. -/
def Admits {s : State} (f : Firing s) : Prop :=
  P.Prepares f ∧
  ∀ sec : CompatibleSection D (P.target f) (P.information f) (P.targetEdgeBase f),
    P.Holds f sec

/-- Resulting multi-action diagram state after an admitted firing. -/
abbrev result {s : State} (f : Firing s) (admitted : P.Admits f) : State :=
  P.preparedResult f admitted.1

/-- **Single-Firing Compatible-Section Refinement (`pullbackAlong`)**:
every `CompatibleSection` of the post-state after an admitted diagram firing pulls back
to a `CompatibleSection` of the pre-state! -/
def pullbackAlong {s : State} (f : Firing s) (admitted : P.Admits f)
    (sec : CompatibleSection D (P.frame (P.result f admitted))
      (P.knowledge (P.result f admitted)) (P.edgeBase (P.result f admitted))) :
    CompatibleSection D (P.frame s) (P.knowledge s) (P.edgeBase s) :=
  let secInfo := sec.pullback (P.preparedSettle f admitted.1)
    (P.result_refines f admitted.1 sec) (P.settle_square f admitted.1)
  secInfo.pullback (P.extension f) (P.information_refines f secInfo) (P.ext_square f)

theorem solvable_start_of_admitted {s : State} (f : Firing s) (admitted : P.Admits f)
    (hpost : Nonempty (CompatibleSection D (P.frame (P.result f admitted))
      (P.knowledge (P.result f admitted)) (P.edgeBase (P.result f admitted)))) :
    Nonempty (CompatibleSection D (P.frame s) (P.knowledge s) (P.edgeBase s)) :=
  Nonempty.elim hpost fun sec => ⟨P.pullbackAlong f admitted sec⟩

/-- A multi-step dependent run over a `DiagramStep`. -/
inductive Run : State → Type (max uS uF)
  | nil (s : State) : Run s
  | cons {s : State} (f : Firing s) (admitted : P.Admits f)
      (rest : Run (P.result f admitted)) : Run s

/-- The final state reached by a diagram run. -/
def Run.last : {s : State} → P.Run s → State
  | _, .nil s => s
  | _, .cons _ _ rest => rest.last

/-- **Multi-Step Diagram-Run Knowledge Refinement (`Run.pullbackStart`)**:
every `CompatibleSection` at the end of a `DiagramStep.Run` pulls back across every
intermediate heterogeneous firing to a `CompatibleSection` of the initial state! -/
def Run.pullbackStart : {s : State} → (r : P.Run s) →
    CompatibleSection D (P.frame r.last) (P.knowledge r.last) (P.edgeBase r.last) →
    CompatibleSection D (P.frame s) (P.knowledge s) (P.edgeBase s)
  | _, .nil _, sec => sec
  | _, .cons f admitted rest, sec =>
      P.pullbackAlong f admitted (rest.pullbackStart sec)

theorem Run.solvable_start {s : State} (r : P.Run s)
    (hlast : Nonempty (CompatibleSection D (P.frame r.last) (P.knowledge r.last)
      (P.edgeBase r.last))) :
    Nonempty (CompatibleSection D (P.frame s) (P.knowledge s) (P.edgeBase s)) :=
  Nonempty.elim hlast fun sec => ⟨Run.pullbackStart P r sec⟩

end DiagramStep

/-- **Singleton Diagram Recovery Theorem**:
on a single-node discrete `FrameDiagram` (one `PackedFrames` `F`, empty edges `Empty`),
existence of a `CompatibleSection` is logically equivalent (`↔`) to single-action
`F.frames.Solvable` — proving `DiagramStep` strictly generalizes `Interface.Step`! -/
abbrev singletonDiagram (F : PackedFrames.{uD}) : FrameDiagram.{uD, 0} PUnit where
  node _ := F
  Edge _ _ := Empty
  edgeMap := fun {_ _} e => nomatch e

theorem singletonDiagram_compatibleSection_iff_solvable (F : PackedFrames.{uD})
    (a : F.Obj) (store : EquationStore (F.Tm a)) :
    Nonempty (CompatibleSection (singletonDiagram F)
      (fun _ => a) (fun _ => store) (fun {_ _} e => nomatch e)) ↔
      F.frames.Solvable store := by
  constructor
  · rintro ⟨sec⟩
    exact ⟨sec.tgt PUnit.unit, sec.sol PUnit.unit, sec.models_node PUnit.unit⟩
  · rintro ⟨b, σ, hmod⟩
    exact ⟨{ tgt := fun _ => b
             sol := fun _ => σ
             models_node := fun _ => hmod
             coh := fun {_ _} e => nomatch e
             comm := fun {_ _} e _ => nomatch e }⟩

/-! ### Concrete 2-Language Firing Positive & Negative Control (`ArithTm ⟶ AffineNat`) -/

namespace CrossLanguageStepControl

open CrossLanguageControl

/-- Simple 2-language state tracking occurrence sets and equation stores at both nodes
(`false = arithPacked`, `true = semNatPacked`). -/
structure TwoLangState where
  present : Bool → Finset ℕ
  arithStore : EquationStore ArithTm
  semStore : EquationStore AffineNat

/-- A cross-language firing selecting per-node occurrences and adding per-node tells. -/
structure TwoLangFiring where
  selection : Bool → Selection ℕ
  arithTell : EquationStore ArithTm
  semTell : EquationStore AffineNat

/-- Concrete `DiagramStep` on `twoLangDiagram : arithPacked ⟶ semNatPacked`. -/
def twoLangStep : DiagramStep twoLangDiagram ℕ TwoLangState (fun _ => TwoLangFiring) where
  frame _ b := match b with | false => PUnit.unit | true => PUnit.unit
  present s := s.present
  knowledge s b := match b with
    | false => s.arithStore
    | true => s.semStore
  edgeBase _ := fun {_ _} e => match e with | .eval => ⟨1, 0⟩
  target _ b := match b with | false => PUnit.unit | true => PUnit.unit
  extension _ b := match b with | false => .var | true => ⟨1, 0⟩
  targetEdgeBase _ := fun {_ _} e => match e with | .eval => ⟨1, 0⟩
  selection f := f.selection
  information {s} f b := match b with
    | false => f.arithTell ++ s.arithStore
    | true => f.semTell ++ s.semStore
  Shapes _ := True
  Holds _ _ := True
  ext_square _ := fun {_ _} e t => by cases e; rfl
  information_refines {s} f sec b := by
    cases b with
    | false =>
        intro eq heq
        exact sec.models_node false eq (List.mem_append_right _ heq)
    | true =>
        intro eq heq
        have h := sec.models_node true eq (List.mem_append_right _ heq)
        have hcomp : substAffine (sec.sol true) ⟨1, 0⟩ = sec.sol true := by
          cases sec.sol true with | mk c k => simp [substAffine]
        change substAffine (substAffine (sec.sol true) ⟨1, 0⟩) eq.1 =
          substAffine (substAffine (sec.sol true) ⟨1, 0⟩) eq.2
        rw [hcomp]
        exact h
  preparedResult {s} f _ :=
    { present := fun b => fire (s.present b) ((f.selection b).commit (T := Unit))
      arithStore := f.arithTell ++ s.arithStore
      semStore := f.semTell ++ s.semStore }
  preparedSettle _ _ b := match b with | false => .var | true => ⟨1, 0⟩
  present_preparedResult _ _ _ := rfl
  settle_square _ _ := fun {_ _} e t => by cases e; rfl
  result_refines {s} f _ sec b := by
    cases b with
    | false =>
        intro eq heq
        exact sec.models_node false eq heq
    | true =>
        intro eq heq
        have h := sec.models_node true eq heq
        have hcomp : substAffine (sec.sol true) ⟨1, 0⟩ = sec.sol true := by
          cases sec.sol true with | mk c k => simp [substAffine]
        change substAffine (substAffine (sec.sol true) ⟨1, 0⟩) eq.1 =
          substAffine (substAffine (sec.sol true) ⟨1, 0⟩) eq.2
        rw [hcomp]
        exact h

def initState : TwoLangState where
  present b := match b with | false => {0} | true => {10}
  arithStore := []
  semStore := []

/-- Positive cross-language firing: takes `0` in `arithPacked`, produces `1`, reads `10`
in `semNatPacked`, tells `var = succ zero` in `arithPacked` and `eval(add zero var) = eval(succ zero)`
in `semNatPacked`. -/
def goodCrossFiring : TwoLangFiring where
  selection b := match b with
    | false => { taken := [0], read := [], made := [1] }
    | true => { taken := [], read := [10], made := [] }
  arithTell := [(.var, .succ .zero)]
  semTell := [(evalArith (.add .zero .var), evalArith (.succ .zero))]

/-- Negative cross-language firing: locally solvable at BOTH nodes (`var = zero` in `arithPacked`
and `eval(var) = succ zero` in `semNatPacked`), yet globally incompatible across `evalFrameMap`! -/
def conflictingCrossFiring : TwoLangFiring where
  selection := goodCrossFiring.selection
  arithTell := [(.var, .zero)]
  semTell := [(evalArith .var, evalArith (.succ .zero))]

/-- **Positive & Negative Cross-Language Firing Controls**:
1. `goodCrossFiring` is ADMITTED by `twoLangStep` and updates `arithPacked`'s occurrences `{0} ↦ {1}`.
2. `conflictingCrossFiring` is locally solvable in BOTH `arithPacked` AND `semNatPacked`,
   yet REFUSED by `twoLangStep.Admits` because no `CompatibleSection` reconciles the two frames! -/
theorem crossLangStep_positive_and_negative_controls :
    twoLangStep.Admits (s := initState) goodCrossFiring ∧
    arithPacked.frames.Solvable (a := PUnit.unit) conflictingCrossFiring.arithTell ∧
    semNatPacked.frames.Solvable (a := PUnit.unit) conflictingCrossFiring.semTell ∧
    ¬ twoLangStep.Admits (s := initState) conflictingCrossFiring := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨⟨trivial, ?_, ?_⟩, fun _ => trivial⟩
    · intro b
      cases b with
      | false =>
          refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [twoLangStep, initState, goodCrossFiring, Selection.commit]
      | true =>
          refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [twoLangStep, initState, goodCrossFiring, Selection.commit]
    · simpa [twoLangStep, initState, goodCrossFiring] using crossLang_positive_section
  · exact ⟨PUnit.unit, .zero, fun eq heq => by rcases List.mem_singleton.mp heq with rfl; rfl⟩
  · exact ⟨PUnit.unit, ⟨0, 1⟩, fun eq heq => by rcases List.mem_singleton.mp heq with rfl; rfl⟩
  · intro hadm
    have hsec := hadm.1.2.2
    have hempty := crossLang_negative_controls.2
    exact Nonempty.elim hsec fun sec =>
      hempty.false (by simpa [twoLangStep, initState, conflictingCrossFiring] using sec)

end CrossLanguageStepControl

end DiagramSteps

end Mettapedia.GSLT.Distinction.SpecSpace
