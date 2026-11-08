import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFibreReflection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerDecidability
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.EmptyRootConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.PartialConstants

/-!
# Second-order fibre conservativity: controls in a concrete package

The package is the cumulative tower with one rigid sort constant `point : U0`; the signature has
one sort and no operators. Every hypothesis of conservativity is discharged in it: the facts of the
weak-head forms, completeness of the algorithmic equality, rigid constants, Church–Rosser of raw
conversion, and injective names.

* **Positive control.** `m(x) ≐ n(x)` has its principal answer `m, n ↦ λx. g x` in the unifier's
  typed βη frame (`point_pattern_principal`), while the raw-conversion frame without η has none
  (`point_pattern_no_principal`).
* **Reflection.** The translation reflects typed βη equality in this package
  (`point_reflects`).
* **Negative control.** A dependent solution of a translated store can use a dependent pair type
  that the second-order side cannot express: in a frame with `p : Σ point. point`, the
  substitution `g ↦ λx. fst p` solves the translated store `g(x) ≐ g(x)`; it is η-long, and its
  η-long form is a projection under an abstraction, which no translation is
  (`offImage_solution`, `offImage_long`, `encode_ne_fst`). Conservativity is a statement about the
  fibre, not about every later frame.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFibre.Controls

open CategoryTheory Interface Interface.Translation
open Mettapedia.OSLF
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ContextualDependentEtaLong

/-! ## The package -/

def point : DeclName := `point

abbrev universe0 : Tm Tower.Head 0 := .head (.sort Tower.zero)

/-- The tower with one sort constant. -/
def pointRules : Rules Tower.Head := Tower.rules.addConstant point universe0

def roles : Roles Tower.Head := fun _ => .rigid

theorem shape : RootShape pointRules roles where
  spine := fun step => False.elim step
  deterministic := fun step => False.elim step

def levels : LevelModel pointRules Nat := { TowerModel.levels (L := Nat) (fun _ => 0) with }

def setting : Setting Tower.Head Nat where
  R := pointRules
  roles := roles
  E := declarative pointRules
  levels := levels
  shape := shape
  constructors := .of_no_inductive fun _ _ role => by cases role

theorem rigid (name : DeclName) : setting.roles name = .rigid := rfl

theorem laws : setting.E.Laws setting.R setting.roles := declarative_laws roles levels

theorem constants : SemanticConstants setting := SemanticConstants.of_rigid laws fun _ => rfl

theorem facts : FormFacts pointRules roles := .ofSemantic (S := setting) laws constants

theorem algebra : CumulativeAlgebra pointRules := { TowerModel.algebra (L := Nat) with }

theorem heads : HeadPreserving pointRules := by
  intro n Γ h h' A same typing
  obtain ⟨u, headTyping, le⟩ := Typed.generation typing
  change LevelTower.HeadTyping h u at headTyping
  change LevelTower.HeadEq h h' at same
  cases headTyping with
  | legacyGround =>
      cases h' with
      | legacyGround => exact Typed.subsume (.headType .legacyGround) le
      | sort _ => exact same.elim
  | sort l =>
      cases h' with
      | legacyGround => exact same.elim
      | sort r =>
          have raise : pointRules.cumulative (.sort (.succ r)) (.sort (.succ l)) := by
            intro ν
            show UniverseLevel.LevelOrder.succ (LevelExpr.eval ν r) ≤
              UniverseLevel.LevelOrder.succ (LevelExpr.eval ν l)
            exact UniverseLevel.LevelOrder.succ_le_succ (le_of_eq (same ν).symm)
          exact Typed.subsume (.cumul (.headType (.sort r)) raise) le

theorem roots : RootPreserving pointRules := by
  intro n Γ l r A _ step
  exact False.elim step

theorem algorithmicConstants : SemanticConstants (algorithmicSetting setting) :=
  SemanticConstants.of_rigid
    (algorithmicSetting_laws (S := setting) laws constants roots heads algebra) fun _ => rfl

theorem complete : AlgorithmicComplete pointRules roles :=
  AlgorithmicComplete.ofSemantic (S := setting) laws constants roots heads algebra
    algorithmicConstants

theorem symmetric : Std.Symm pointRules.headEq := by
  refine ⟨fun a b same => ?_⟩
  change LevelTower.HeadEq a b at same
  change LevelTower.HeadEq b a
  cases a with
  | legacyGround => cases b with
    | legacyGround => trivial
    | sort _ => exact same.elim
  | sort l => cases b with
    | legacyGround => exact same.elim
    | sort r => exact fun ν => (same ν).symm

theorem church : ConversionCoherence.ChurchRosser pointRules :=
  EmptyRootConversion.churchRosser pointRules rfl symmetric

/-! ## The signature and its realization -/

def pointSig : Binding.Signature where
  Srt := Unit
  Op := fun _ => Empty
  arity := fun o => o.elim

def names : BindingSignatureEmbedding.Names pointSig := ⟨fun _ => point, fun o => o.elim⟩

def realization : BindingSignatureEmbedding.Realization names pointRules where
  typeUniverse := .sort Tower.zero
  above := .sort (.succ Tower.zero)
  joined := .sort (.max Tower.zero Tower.zero)
  universeTyped := LevelTower.HeadTyping.sort Tower.zero
  universeIs := .sort Tower.zero
  aboveIs := .sort (.succ Tower.zero)
  joinSelf := .sorts Tower.zero Tower.zero
  collapseSelf := by
    change LevelTower.Cumulative (.sort (.max Tower.zero Tower.zero)) (.sort Tower.zero)
    intro valuation
    simp [LevelExpr.eval]
  sortLookup := fun _ => rfl
  operatorLookup := fun o => o.elim

/-- The one sort. -/
abbrev star : pointSig.Srt := ()

theorem sortInjective : Function.Injective names.sort := fun _ _ _ => rfl

theorem operatorInjective {s : pointSig.Srt} : Function.Injective (names.operator (sort := s)) :=
  fun o => o.elim

/-- The second-order step inside the unifier's frame of the package. -/
abbrev Ψ := fibre (S := setting) facts roots heads church names realization

/-! ## Reflection and the positive control -/

/-- **The translation reflects typed βη equality in the package.** -/
theorem point_reflects : Ψ.Reflects :=
  fibre_reflects (S := setting) facts roots heads algebra complete rigid church names realization
    sortInjective @operatorInjective

/-- **Positive control**: with η, `m(x) ≐ n(x)` has a principal answer in the unifier's frame. -/
theorem point_pattern_principal :
    (ContextualDependentEta.frames setting.levels).Principal
      (a := Ψ.obj (pairFrame star)) (m := Ψ.obj (unaryFrame star))
      (Ψ.store (patternStore star)) (Ψ.hom (collapse star)) :=
  fibre_pattern_principal (S := setting) facts roots heads church names realization star

/-- **Without η there is none**: the raw-conversion frames of the same package. -/
theorem point_pattern_no_principal :
    ¬ ∃ (Θ : FormationSensitiveContextual.Context pointRules)
      (answer : Θ ⟶ ctxOf names realization (pairFrame star)),
      (Dependent.frames pointRules).Principal (a := ctxOf names realization (pairFrame star)) (m := Θ)
        ((translation names realization).store (patternStore star)) answer :=
  pattern_no_principal names realization star rfl symmetric

/-! ## The negative control: an off-image solution -/

def pointType {n : Nat} : Tower.Tm n := .const point

def pointPair {n : Nat} : Tower.Tm n := .sigma pointType pointType

theorem point_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed pointRules Γ pointType (.head (.sort Tower.zero)) :=
  Derivable.const (rfl : pointRules.constantType point = some universe0)
    (.headType (.sort Tower.zero)) (.sort _)

theorem pointPair_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed pointRules Γ pointPair (.head (.sort (.max Tower.zero Tower.zero))) :=
  .sigmaForm (point_typed Γ) (.sort _) (point_typed _) (.sort _) (.sorts _ _)

/-- The frame `p : Σ point. point`. -/
def pairs : TypedContextual.Context pointRules :=
  ⟨1, .snoc .nil pointPair, .snoc .nil ⟨_, .sort _, pointPair_typed _⟩⟩

/-- `λx. fst p`. -/
def projection : Tower.Tm 1 := .lam (.fst (.var 1))

theorem projection_typed :
    Typed pointRules pairs.raw projection (.pi pointType pointType) :=
  .lamIntro (.cumul (.piForm (point_typed _) (.sort _) (point_typed _) (.sort _)
      (.sorts _ _)) (realization.collapseSelf))
    (.sort _) (.fstElim (B := pointType) (Derivable.var 1))

/-- The unary store `g(x) ≐ g(x)`. -/
def unaryStore : EquationStore (Binding.ContextualFamily.Observation pointSig (unaryFrame star).get) :=
  [(occurrence (unaryFrame star) (gIdx star), occurrence (unaryFrame star) (gIdx star))]

/-- The substitution `g ↦ λx. fst p`. -/
def offImage : pairs ⟶ Ψ.obj (unaryFrame star) where
  substitution := consSub projection (fun k => k.elim0)
  typed := by
    intro (i : Fin 1)
    refine Fin.cases ?_ (fun k => k.elim0) i
    exact projection_typed

/-- **The off-image substitution solves the translated store.** -/
theorem offImage_solution :
    (ContextualDependentEta.frames setting.levels).Models offImage (Ψ.store unaryStore) := by
  intro e member
  simp only [Translation.FrameMap.store, unaryStore, List.map_cons, List.map_nil,
    List.mem_singleton] at member
  subst member
  exact ((ContextualDependentEta.frames setting.levels).equivalence _).refl _

/-- Its component is η-long, a projection under an abstraction. -/
theorem offImage_long :
    Long pointRules roles (.term pairs.raw projection (.pi pointType pointType)) := by
  have formed : CtxFormed pointRules (.snoc pairs.raw pointType) :=
    .snoc pairs.formed ⟨_, .sort _, point_typed _⟩
  have isPoint : ∀ {n : Nat} (Γ : Tower.Ctx n), IsType pointRules Γ pointType :=
    fun Γ => ⟨_, .sort _, point_typed Γ⟩
  have isPair : IsType pointRules (.snoc pairs.raw pointType) pointPair :=
    ⟨_, .sort _, pointPair_typed _⟩
  have spine : Long pointRules roles (.spine (.snoc pairs.raw pointType) (.fst (.var 1)) pointType) :=
    .fst (.var 1 (IsType.refl isPair)) (IsType.refl isPair) (IsType.refl (isPoint _))
  have base : Base pointRules (.snoc pairs.raw pointType) pointType :=
    sort_base (S := setting) facts rigid names formed ()
  exact .lam (IsType.refl ⟨_, .sort _, .cumul (.piForm (point_typed _) (.sort _) (point_typed _)
      (.sort _) (.sorts _ _)) realization.collapseSelf⟩) (isPoint _) projection_typed
    (.neutral spine (IsType.below_refl (isPoint _))
      (.fstElim (B := pointType) (Derivable.var 1)) base)

/-- Every η-long form of the off-image component is `λx. fst p` itself, up to heads. -/
theorem offImage_normal {v : Tower.Tm 1}
    (normal : NormalForm pointRules roles pairs.raw projection v (.pi pointType pointType)) :
    SameUpToHeads pointRules projection v :=
  normalForm_unique (S := setting) facts roots heads algebra complete pairs.formed
    ⟨offImage_long, .refl projection_typed⟩ normal

/-- **No translation is a projection.** -/
theorem encode_ne_fst {sig : Binding.Signature} (nm : BindingSignatureEmbedding.Names sig)
    (M : List (Binding.MetaArity sig)) {Γ : Binding.Ctx sig} {s : sig.Srt}
    (t : Binding.Term (Sig sig M) Γ s) (u : Tm Tower.Head (M.length + Γ.length)) :
    Translation.encode (Head := Tower.Head) nm M t ≠ .fst u := by
  have applyVec_ne : ∀ {n p : Nat} (f : Tm Tower.Head n) (w : Sub Tower.Head p n)
      (u : Tm Tower.Head n), (∀ x, f ≠ .fst x) → applyVec f w ≠ .fst u := by
    intro n p
    induction p with
    | zero => intro f w u hf; exact hf u
    | succ p ih => intro f w u _; exact ih (.app f (w 0)) (fun j => w j.succ) u (fun _ e => nomatch e)
  have spine_ne : ∀ {n p : Nat} (f : Tm Tower.Head n) (w : Sub Tower.Head p n)
      (u : Tm Tower.Head n), (∀ x, f ≠ .fst x) → spine f w ≠ .fst u := by
    intro n p f w u hf
    cases p with
    | zero => exact hf u
    | succ p => exact fun e => nomatch e
  match t with
  | .var _ => exact fun e => nomatch e
  | .op (.inl _) _ => exact applyVec_ne _ _ u (fun _ e => nomatch e)
  | .op (.inr (.mk _)) _ => exact spine_ne _ _ u (fun _ e => nomatch e)

end ContextualDependentFibre.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
