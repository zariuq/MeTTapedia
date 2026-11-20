import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.Synthesis

/-!
# Refusing a mistyped row: a principal type against the normal form of the declared type

The package's family never refutes (`vecRound_never_refutes`), so `vecAdmits?` says "no" only on
refuted information, and on a mistyped row whose information is solvable it says nothing
(`nilFirst_undecided`). A refusal must then show that **at one solution of what the match teaches**
the body is not typed at the declared type: typed after the match means typed at every solution.

`refute?` does this for a pair componentwise, and otherwise for a body whose type is principal by
generation:

* **a pair** against a declared type whose normal form is a pair type: its first component against
  the domain, its second against the codomain read at the first (`pair_parts`); against a neutral or
  inductive normal form, a pair has no type at all (`pair_not_rigid`);

* **a variable**, every type of which lies above its declared type, and **a constant**, every type of
  which lies above its declaration (`principal?`);
* the declared type at the solution is run to a normal form by the package's executable reduction
  (`vecNormalize`, sound: it is reached by computation, so it is an equal type);
* the principal type must be **rigid** (a neutral type, or an inductive type constant: usable only at
  types equal to it, `rigid?`), and **apart** from the normal form (`apart?`): an inductive type
  against a neutral type or a universe, function or pair type, two neutral types with different
  elimination heads, or two neutral applications whose last arguments are neutral with different
  heads (equal neutral types have equal arguments, `neutral_application_arguments`; neutral terms
  with different heads are equal at no type, `not_equal_of_neutral_heads`, from the completeness of
  the package's conversion algorithm).

Every refutation it returns is a theorem (`refute?` carries the proof). Outside these shapes it
returns nothing, which the checker reads as "not decided".
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Vectors.Checker

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg)

/-! ## Neutral types and inductive type constants, recognized with their proofs -/

/-- **Recognized neutral terms**: variables, `vec A k` stuck on a neutral length, `add a b` stuck on a
neutral first argument, and applications of neutral terms. -/
def neutral? : {n : Nat} → (t : Tower.Tm n) → Option (PLift (Neutral TowerVectorsModel.roles t))
  | _, .var i => some ⟨.var i⟩
  | _, .app (.app (.const c) A) k =>
      if h : c = TowerVectorsModel.vec then
        (neutral? k).bind fun nk => some ⟨by subst h; exact TowerVectorsConversion.vec_stuck A nk.down⟩
      else if h' : c = TowerVectorsModel.add then
        (neutral? A).bind fun na => some ⟨by
          subst h'
          exact Neutral.stuck_single (before := []) (after := [k]) TowerVectorsModel.roles_add rfl na.down⟩
      else none
  | _, .app f _ => (neutral? f).bind fun nf => some ⟨.app nf.down⟩
  | _, _ => none

/-- An inductive type constant of the package. -/
def InductiveConst {n : Nat} (t : Tower.Tm n) : Prop :=
  ∃ T constructors, TowerVectorsModel.roles T = .inductive constructors ∧ t = .const T

/-- **Recognized inductive type constants**: the numbers and the unit type. -/
def inductiveConst? {n : Nat} : (t : Tower.Tm n) → Option (PLift (InductiveConst t))
  | .const c =>
      if h : c = TowerNumbersModel.num then some ⟨⟨_, _, TowerVectorsModel.roles_num, by rw [h]⟩⟩
      else if h' : c = TowerVectorsModel.unit then some ⟨⟨_, _, TowerVectorsModel.roles_unit, by rw [h']⟩⟩
      else none
  | _ => none

/-! ## Rigid types -/

section Apart

variable {n : Nat} {Γ : Ctx Tower.Head n}

/-- A type usable only at types equal to it: no universe, function or pair type. -/
def RigidAt (Γ : Ctx Tower.Head n) (P : Tower.Tm n) : Prop :=
  (∀ u, pkg.isUniverse u → ¬ TypeEq pkg Γ P (.head u)) ∧ (∀ A B, ¬ TypeEq pkg Γ P (.pi A B)) ∧
    ∀ A B, ¬ TypeEq pkg Γ P (.sigma A B)

theorem rigid_of_neutral (formed : CtxFormed pkg Γ) {P : Tower.Tm n}
    (neutral : Neutral TowerVectorsModel.roles P) : RigidAt Γ P :=
  ⟨fun _ _ e => (TypeEq.neutral_form (TowerVectorsModel.facts level1) e formed neutral
      (.inl ⟨_, rfl⟩)).not_former.1 _ rfl,
    fun _ _ e => (TypeEq.neutral_form (TowerVectorsModel.facts level1) e formed neutral
      (.inr (.inl ⟨_, _, rfl⟩))).not_former.2.1 _ _ rfl,
    fun _ _ e => (TypeEq.neutral_form (TowerVectorsModel.facts level1) e formed neutral
      (.inr (.inr (.inl ⟨_, _, rfl⟩)))).not_former.2.2.1 _ _ rfl⟩

theorem rigid_of_inductive (formed : CtxFormed pkg Γ) {P : Tower.Tm n} (inductive' : InductiveConst P) :
    RigidAt Γ P := by
  obtain ⟨T, constructors, role, rfl⟩ := inductive'
  exact ⟨fun _ _ e => TypeEq.inductive_ne_head (TowerVectorsModel.facts level1) role formed e,
    fun _ _ e => TypeEq.inductive_ne_pi (TowerVectorsModel.facts level1) role formed e,
    fun _ _ e => TypeEq.inductive_ne_sigma (TowerVectorsModel.facts level1) role formed e⟩

/-- **Rigidity, recognized.** -/
def rigid? (Γ : Ctx Tower.Head n) (P : Tower.Tm n) : Option (PLift (CtxFormed pkg Γ → RigidAt Γ P)) :=
  match neutral? P with
  | some neutral => some ⟨fun formed => rigid_of_neutral formed neutral.down⟩
  | none => (inductiveConst? P).bind fun i => some ⟨fun formed => rigid_of_inductive formed i.down⟩

/-! ## Apart types -/

/-- **An inductive type is no neutral type.** -/
theorem apart_inductive_neutral (formed : CtxFormed pkg Γ) {P T : Tower.Tm n} (inductive' : InductiveConst P)
    (neutral : Neutral TowerVectorsModel.roles T) : ¬ TypeEq pkg Γ P T := by
  intro e
  obtain ⟨c, constructors, role, rfl⟩ := inductive'
  exact (TypeEq.neutral_form (TowerVectorsModel.facts level1) e.symm formed neutral
    (.inr (.inr (.inr (.inr (.inr ⟨c, constructors, role, rfl⟩)))))).ne_inductive role rfl

/-- **Neutral types with different elimination heads are not equal.** -/
theorem apart_neutral_heads (formed : CtxFormed pkg Γ) {P T : Tower.Tm n}
    (neutralP : Neutral TowerVectorsModel.roles P) (neutralT : Neutral TowerVectorsModel.roles T)
    (different : eliminationHead P ≠ eliminationHead T) : ¬ TypeEq pkg Γ P T := by
  rintro ⟨_, -, e⟩
  exact not_equal_of_neutral_heads (S := vecS) (TowerVectorsConversion.complete level1) formed neutralP
    neutralT different e

/-- **Neutral applications whose last arguments are neutral with different heads are not equal.** -/
theorem apart_last_arguments (formed : CtxFormed pkg Γ) {f g a b : Tower.Tm n}
    (neutralP : Neutral TowerVectorsModel.roles (.app f a)) (neutralT : Neutral TowerVectorsModel.roles (.app g b))
    (neutralA : Neutral TowerVectorsModel.roles a) (neutralB : Neutral TowerVectorsModel.roles b)
    (different : eliminationHead a ≠ eliminationHead b) : ¬ TypeEq pkg Γ (.app f a) (.app g b) := by
  intro e
  obtain ⟨_, arguments⟩ := TowerVectorsConversion.neutral_application_arguments (lv := level1) formed neutralP
    neutralT e
  exact not_equal_of_neutral_heads (S := vecS) (TowerVectorsConversion.complete level1) formed neutralA
    neutralB different arguments

/-- The last-argument clash, recognized. -/
def lastApart? (Γ : Ctx Tower.Head n) : (P T : Tower.Tm n) → Option (PLift (CtxFormed pkg Γ → ¬ TypeEq pkg Γ P T))
  | .app f a, .app g b =>
      match neutral? (.app f a), neutral? (.app g b), neutral? a, neutral? b with
      | some np, some nt, some na, some nb =>
          if different : eliminationHead a ≠ eliminationHead b then
            some ⟨fun formed => apart_last_arguments formed np.down nt.down na.down nb.down different⟩
          else none
      | _, _, _, _ => none
  | _, _ => none

/-- **An inductive type is no universe, function or pair type**, recognized. -/
def formerApart? (Γ : Ctx Tower.Head n) (P : Tower.Tm n) :
    (T : Tower.Tm n) → Option (PLift (CtxFormed pkg Γ → ¬ TypeEq pkg Γ P T))
  | .head _ => (inductiveConst? P).bind fun i => some ⟨fun formed e => by
      obtain ⟨c, constructors, role, rfl⟩ := i.down
      exact TypeEq.inductive_ne_head (TowerVectorsModel.facts level1) role formed e⟩
  | .pi _ _ => (inductiveConst? P).bind fun i => some ⟨fun formed e => by
      obtain ⟨c, constructors, role, rfl⟩ := i.down
      exact TypeEq.inductive_ne_pi (TowerVectorsModel.facts level1) role formed e⟩
  | .sigma _ _ => (inductiveConst? P).bind fun i => some ⟨fun formed e => by
      obtain ⟨c, constructors, role, rfl⟩ := i.down
      exact TypeEq.inductive_ne_sigma (TowerVectorsModel.facts level1) role formed e⟩
  | _ => none

/-- **Apartness, recognized**, with its proof. -/
def apart? (Γ : Ctx Tower.Head n) (P T : Tower.Tm n) : Option (PLift (CtxFormed pkg Γ → ¬ TypeEq pkg Γ P T)) :=
  match inductiveConst? P, neutral? T with
  | some i, some nt => some ⟨fun formed => apart_inductive_neutral formed i.down nt.down⟩
  | _, _ =>
      match neutral? P, inductiveConst? T with
      | some np, some i => some ⟨fun formed e => apart_inductive_neutral formed i.down np.down e.symm⟩
      | _, _ =>
          match neutral? P, neutral? T with
          | some np, some nt =>
              if different : eliminationHead P ≠ eliminationHead T then
                some ⟨fun formed => apart_neutral_heads formed np.down nt.down different⟩
              else lastApart? Γ P T
          | _, _ => formerApart? Γ P T

end Apart

/-! ## Principal types by generation, and the refutation -/

/-- **A principal type by generation**: every type of a variable lies above its declared type, every
type of a constant above its declaration. -/
def principal? {n : Nat} (Γ : Ctx Tower.Head n) :
    (t : Tower.Tm n) → Option ((P : Tower.Tm n) × PLift (∀ {T : Tower.Tm n}, Typed pkg Γ t T → TypeLe pkg Γ P T))
  | .var i => some ⟨Ctx.lookup Γ i, ⟨fun typed => Typed.generation typed⟩⟩
  | .const c =>
      match known : pkg.constantType c with
      | some type => some ⟨liftClosed type, ⟨fun typed => by
          obtain ⟨type', _, declared, _, _, le⟩ := Typed.generation typed
          rw [known] at declared
          cases declared
          exact le⟩⟩
      | none => none
  | _ => none

/-- **A typing refuted through the principal type**: the term's principal type is rigid and apart from
the normal form of the type. -/
def principalRefute? (fuel : Nat) {n : Nat} (Γ : Ctx Tower.Head n) (t T : Tower.Tm n) :
    Option (PLift (CtxFormed pkg Γ → IsType pkg Γ T → ¬ Typed pkg Γ t T)) :=
  match principal? Γ t with
  | none => none
  | some ⟨P, principal⟩ =>
      match ran : vecNormalize level1 fuel T with
      | none => none
      | some normal =>
          match rigid? Γ P, apart? Γ P normal with
          | some rigid, some apart =>
              some ⟨fun formed typeT typed => by
                have below : Below pkg Γ P T := TypeLe.toBelow (principal.down typed) typeT
                have toNormal : TypeEq pkg Γ T normal :=
                  Reduces.typeEq (S := vecS) (TowerVectorsModel.facts level1) (TowerVectorsModel.roots level1)
                    (TowerVectorsModel.heads level1) formed (vecNormalize_sound level1 ran) typeT
                have equal : TypeEq pkg Γ P normal :=
                  Below.rigid (S := vecS) (.subTrans below toNormal.below) formed (rigid.down formed).1
                    (rigid.down formed).2.1 (rigid.down formed).2.2
                exact apart.down formed equal⟩
          | _, _ => none

/-! ## Pairs -/

section Pairs

variable {n : Nat} {Γ : Ctx Tower.Head n}

/-- **A pair is no term of a neutral type, nor of an inductive type.** -/
theorem pair_not_rigid (formed : CtxFormed pkg Γ) {a b T normal : Tower.Tm n} (typeT : IsType pkg Γ T)
    (toNormal : TypeEq pkg Γ T normal)
    (rigidNormal : Neutral TowerVectorsModel.roles normal ∨ InductiveConst normal) :
    ¬ Typed pkg Γ (.pair a b) T := by
  intro typed
  obtain ⟨A', B', u, tSigma, hu, -, -, le⟩ := Typed.generation typed
  have below : Below pkg Γ (.sigma A' B') normal := .subTrans (TypeLe.toBelow le typeT) toNormal.below
  obtain ⟨A₁, B₁, eNormal, -, -⟩ := Below.sigma_source (S := vecS) (TowerVectorsModel.facts level1) below formed
    (IsType.refl ⟨u, hu, tSigma⟩)
  rcases rigidNormal with neutral | inductive'
  · exact (TypeEq.neutral_form (TowerVectorsModel.facts level1) eNormal formed neutral
      (.inr (.inr (.inl ⟨_, _, rfl⟩)))).not_former.2.2.1 _ _ rfl
  · obtain ⟨c, constructors, role, rfl⟩ := inductive'
    exact TypeEq.inductive_ne_sigma (TowerVectorsModel.facts level1) role formed eNormal

/-- **A pair at a pair type has its components at the parts**, the second at the codomain read at the
first. -/
theorem pair_parts (formed : CtxFormed pkg Γ) {a b T X : Tower.Tm n} {Y : Tower.Tm (n + 1)}
    (toSigma : TypeEq pkg Γ T (.sigma X Y)) (typed : Typed pkg Γ (.pair a b) T) :
    IsType pkg Γ X ∧ Typed pkg Γ a X ∧ IsType pkg Γ (inst0 a Y) ∧ Typed pkg Γ b (inst0 a Y) := by
  obtain ⟨w, hw, e⟩ := toSigma
  have typeSigma : IsType pkg Γ (.sigma X Y) := ⟨w, hw, (Equal.typed (S := vecS) e formed).2⟩
  obtain ⟨partX, v, hv, family⟩ := IsType.sigma_parts typeSigma
  obtain ⟨ta, tb⟩ := Typed.pair_inv (S := vecS) (TowerVectorsModel.facts level1)
    (Typed.convType typed ⟨w, hw, e⟩) formed
  exact ⟨partX, ta, ⟨v, hv, Typed.instantiate family ta⟩, tb⟩

end Pairs

/-- **The refutation of a typing**, with its proof: a pair componentwise against the normal form of the
type when it is a pair type, or because that normal form is neutral or an inductive type; any other
term through its principal type. -/
def refute? (fuel : Nat) {n : Nat} (Γ : Ctx Tower.Head n) :
    (t T : Tower.Tm n) → Option (PLift (CtxFormed pkg Γ → IsType pkg Γ T → ¬ Typed pkg Γ t T))
  | .pair a b, T =>
      match ran : vecNormalize level1 fuel T with
      | none => none
      | some (.sigma X Y) =>
          match refute? fuel Γ a X with
          | some first =>
              some ⟨fun formed typeT typed => by
                have toSigma : TypeEq pkg Γ T (.sigma X Y) :=
                  Reduces.typeEq (S := vecS) (TowerVectorsModel.facts level1) (TowerVectorsModel.roots level1)
                    (TowerVectorsModel.heads level1) formed (vecNormalize_sound level1 ran) typeT
                obtain ⟨typeX, ta, -, -⟩ := pair_parts formed toSigma typed
                exact first.down formed typeX ta⟩
          | none =>
              (refute? fuel Γ b (inst0 a Y)).bind fun second =>
                some ⟨fun formed typeT typed => by
                  have toSigma : TypeEq pkg Γ T (.sigma X Y) :=
                    Reduces.typeEq (S := vecS) (TowerVectorsModel.facts level1) (TowerVectorsModel.roots level1)
                      (TowerVectorsModel.heads level1) formed (vecNormalize_sound level1 ran) typeT
                  obtain ⟨-, -, typeB, tb⟩ := pair_parts formed toSigma typed
                  exact second.down formed typeB tb⟩
      | some normal =>
          match neutral? normal, inductiveConst? normal with
          | some neutral, _ =>
              some ⟨fun formed typeT => pair_not_rigid formed typeT
                (Reduces.typeEq (S := vecS) (TowerVectorsModel.facts level1) (TowerVectorsModel.roots level1)
                  (TowerVectorsModel.heads level1) formed (vecNormalize_sound level1 ran) typeT) (.inl neutral.down)⟩
          | none, some inductive' =>
              some ⟨fun formed typeT => pair_not_rigid formed typeT
                (Reduces.typeEq (S := vecS) (TowerVectorsModel.facts level1) (TowerVectorsModel.roots level1)
                  (TowerVectorsModel.heads level1) formed (vecNormalize_sound level1 ran) typeT)
                (.inr inductive'.down)⟩
          | none, none => none
  | t, T => principalRefute? fuel Γ t T

end NativeTypesOnTheStep.Computing.Vectors.Checker

#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.neutral?
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.inductiveConst?
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.rigid_of_neutral
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.rigid_of_inductive
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.apart_inductive_neutral
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.apart_neutral_heads
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.apart_last_arguments
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.apart?
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.principal?
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.principalRefute?
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.pair_not_rigid
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.pair_parts
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.refute?

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
