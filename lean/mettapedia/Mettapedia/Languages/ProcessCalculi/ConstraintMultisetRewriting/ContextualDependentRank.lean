import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentOccursFull

/-!
# A rank that decomposition lowers

The worklist rank `size` counts declarations, then equations. A decomposition keeps the declarations
and replaces one equation by two or three, so it raises `size`; R94's decompositions therefore commit
only when a following rule removes a declaration or refutes.

The **weight rank** counts declarations, then the **normal weight** of the store: for every side of every
equation, the number of nodes of its η-long β-normal form (R88), abstractions not counted (`weight`).
Normal forms are unique up to heads, so the normal weight of a judged term is well defined
(`sideWeight_eq`), and it depends only on the term up to typed equality: η-expansion and β-reduction do
not change it.

Every decomposition lowers the normal weight by two (`formerParts_weight`):

* `Id C a b ≐ Id C' a' b'` becomes `C ≐ C'`, `a ≐ a'`, `b ≐ b'`; the normal form of an identity type
  is the identity type of the normal forms of its parts;
* `Π A B ≐ Π A' B'` becomes `A ≐ A'` and the family twin `λ x. B ≐ λ x. B'`; the normal form of the
  twin's side is `λ x. E` for the normal form `E` of `B`, and abstractions weigh nothing;
* `(a, b) ≐ (a', b')` becomes `a ≐ a'` and `b ≐ b'`.

The conversion scan removes equations and so lowers it too (`scan_weight_lt`), and every rule that
removes a declaration lowers its first component. The rank lives in `ℕ × ℕ` ordered
lexicographically, which is well founded (`weightRank_wf`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRank

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentInPlace
open ContextualDependentRigidFormers ContextualDependentEtaLong ContextualDependentOccursCheck

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Weights -/

/-- **The weight of a code**: its number of nodes, abstractions not counted. -/
def weight : {n : Nat} → Tm Head n → Nat
  | _, .var _ => 1
  | _, .const _ => 1
  | _, .head _ => 1
  | _, .pi A B => weight A + weight B + 1
  | _, .sigma A B => weight A + weight B + 1
  | _, .id A x y => weight A + weight x + weight y + 1
  | _, .lam b => weight b
  | _, .app f a => weight f + weight a + 1
  | _, .pair a b => weight a + weight b + 1
  | _, .fst p => weight p + 1
  | _, .snd p => weight p + 1
  | _, .refl z => weight z + 1

theorem weight_pos : ∀ {n : Nat} (t : Tm Head n), 0 < weight t
  | _, .var _ | _, .const _ | _, .head _ => by simp only [weight]; omega
  | _, .pi _ _ | _, .sigma _ _ | _, .id _ _ _ | _, .app _ _ | _, .pair _ _ | _, .fst _ | _, .snd _
  | _, .refl _ => by simp only [weight]; omega
  | _, .lam b => by simp only [weight]; exact weight_pos b

/-- Terms that are the same up to heads have the same weight. -/
theorem weight_of_same {R : Rules Head} {n : Nat} {s t : Tm Head n} (same : SameUpToHeads R s t) :
    weight s = weight t := by
  induction same with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi _ _ ih₁ ih₂ => simp only [weight, ih₁, ih₂]
  | sigma _ _ ih₁ ih₂ => simp only [weight, ih₁, ih₂]
  | id _ _ _ ih₁ ih₂ ih₃ => simp only [weight, ih₁, ih₂, ih₃]
  | lam _ ih => simp only [weight, ih]
  | app _ _ ih₁ ih₂ => simp only [weight, ih₁, ih₂]
  | pair _ _ ih₁ ih₂ => simp only [weight, ih₁, ih₂]
  | fst _ ih => simp only [weight, ih]
  | snd _ ih => simp only [weight, ih]
  | refl _ ih => simp only [weight, ih]

/-! ## Normal weights -/

section Normal

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- **The normal weight of a judged term**: the weight of its η-long normal form at its type. -/
noncomputable def sideWeight {Θ : Context S.R} (side : TotalTerm Θ) : Nat :=
  weight (Classical.choose (long_exists facts roots heads algebra rigid complete Θ.formed side.2.typed))

include facts roots heads algebra complete in
/-- **The normal weight is the weight of any normal form.** -/
theorem sideWeight_eq {Θ : Context S.R} (side : TotalTerm Θ) {v : Tm Head Θ.arity}
    (normal : NormalForm S.R S.roles Θ.raw side.2.code v side.1.code) :
    sideWeight facts roots heads algebra rigid complete side = weight v := by
  have chosen := Classical.choose_spec (long_exists facts roots heads algebra rigid complete Θ.formed side.2.typed)
  exact weight_of_same (long_unique facts roots heads algebra complete Θ.formed chosen.1 normal.1
    (.trans (.symm chosen.2) normal.2))

/-- The normal weight of an equation: both sides. -/
noncomputable def equationWeight {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Nat :=
  sideWeight facts roots heads algebra rigid complete equation.1 +
    sideWeight facts roots heads algebra rigid complete equation.2

/-- The normal weight of a store: every equation. -/
noncomputable def storeWeight {Θ : Context S.R} : EquationStore (TotalTerm Θ) → Nat
  | [] => 0
  | equation :: rest => equationWeight facts roots heads algebra rigid complete equation + storeWeight rest

/-- **The weight rank**: declarations, then the normal weight of the store. -/
noncomputable def weightRank {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Nat × Nat :=
  (Θ.arity, storeWeight facts roots heads algebra rigid complete problem)

/-- **The rank is well founded**: lexicographic pairs of natural numbers. -/
theorem weightRank_wf : WellFounded ContextualDependentWorklist.Below := below_wf

theorem storeWeight_append {Θ : Context S.R} (first second : EquationStore (TotalTerm Θ)) :
    storeWeight facts roots heads algebra rigid complete (first ++ second) =
      storeWeight facts roots heads algebra rigid complete first +
        storeWeight facts roots heads algebra rigid complete second := by
  induction first with
  | nil => simp only [List.nil_append, storeWeight, Nat.zero_add]
  | cons equation rest ih => simp only [List.cons_append, storeWeight, ih]; omega

include facts roots heads algebra complete in
theorem sideWeight_pos {Θ : Context S.R} (side : TotalTerm Θ) :
    0 < sideWeight facts roots heads algebra rigid complete side := by
  unfold sideWeight
  exact weight_pos _

include facts roots heads algebra complete in
theorem equationWeight_pos {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    0 < equationWeight facts roots heads algebra rigid complete equation := by
  have := sideWeight_pos facts roots heads algebra rigid complete equation.1
  unfold equationWeight
  omega

/-! ## Normal forms of the formers -/

theorem universe_typeEq {n : Nat} (Γ : Ctx Head n) {u : Head} (hu : S.R.isUniverse u) :
    TypeEq S.R Γ (.head u) (.head u) :=
  (universe_isType Γ hu).refl

include facts roots heads algebra rigid complete in
/-- **The normal form of a type at a universe** is a normal type. -/
theorem universe_normalForm {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {B : Tm Head n} {u : Head}
    (hu : S.R.isUniverse u) (tB : Typed S.R Γ B (.head u)) :
    ∃ Z, Long S.R S.roles (.type Γ Z) ∧ NormalForm S.R S.roles Γ B Z (.head u) := by
  obtain ⟨Z, lZ, atZ⟩ := long_type_exists facts roots heads algebra rigid complete formed ⟨u, hu, tB⟩
  obtain ⟨tZ, eZ⟩ := atZ hu tB
  exact ⟨Z, lZ, .univ hu (universe_typeEq Γ hu) tZ lZ, eZ⟩

include facts roots heads algebra complete in
/-- **The normal form of a binder type** at a universe is the binder of the normal forms of its parts. -/
theorem binder_normalForm (isPi : Bool) {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {A D : Tm Head n}
    {B E : Tm Head (n + 1)} {u : Head} (hu : S.R.isUniverse u) (tA : Typed S.R Γ A (.head u))
    (tB : Typed S.R (.snoc Γ A) B (.head u)) (lD : Long S.R S.roles (.type Γ D))
    (nA : NormalForm S.R S.roles Γ A D (.head u)) (lE : Long S.R S.roles (.type (.snoc Γ A) E))
    (nB : NormalForm S.R S.roles (.snoc Γ A) B E (.head u)) :
    NormalForm S.R S.roles Γ (binder isPi A B) (binder isPi D E) (.head u) := by
  have AD : TypeEq S.R Γ A D := ⟨u, hu, nA.2⟩
  have there : CtxEq S.R (.snoc Γ A) (.snoc Γ D) := .snoc (CtxEq.refl Γ formed) AD.symm
  have back : CtxEq S.R (.snoc Γ D) (.snoc Γ A) := .snoc (CtxEq.refl Γ formed) AD
  have lE' : Long S.R S.roles (.type (.snoc Γ D) E) := lE.stable S.levels there back
  have tD : Typed S.R Γ D (.head u) := nA.1.typed
  have tE' : Typed S.R (.snoc Γ D) E (.head u) := Typed.stable nB.1.typed there
  obtain ⟨j, joined, below⟩ := self_join algebra hu
  have tW : Typed S.R Γ (binder isPi D E) (.head u) :=
    Derivable.cumul (binder_formed isPi tD hu tE' hu joined) below
  have tLeft : Typed S.R Γ (binder isPi A B) (.head u) :=
    Derivable.cumul (binder_formed isPi tA hu tB hu joined) below
  refine ⟨.univ hu (universe_typeEq Γ hu) tW (binder_long isPi lD lE' ⟨u, hu, tW⟩), ?_⟩
  exact equal_of_typeEq facts roots heads algebra complete formed hu tLeft tW
    ((typeEq_binder_iff facts isPi formed).mpr ⟨AD, ⟨u, hu, nB.2⟩⟩)

/-- **The normal form of a family twin's side** `λ x. B` at `Π A U` is `λ x. E`. -/
theorem family_normalForm {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B E : Tm Head (n + 1)} {u v : Head}
    (hv : S.R.isUniverse v) (tPi : Typed S.R Γ (.pi A (.head u)) (.head v)) (isA : IsType S.R Γ A)
    (nB : NormalForm S.R S.roles (.snoc Γ A) B E (.head u)) :
    NormalForm S.R S.roles Γ (.lam B) (.lam E) (.pi A (.head u)) :=
  ⟨.lam (IsType.refl ⟨v, hv, tPi⟩) isA (.lamIntro tPi hv nB.1.typed) nB.1, .lamCong tPi hv nB.2⟩

/-- **The normal form of an identity type** at a universe is the identity type of the normal forms. -/
theorem id_normalForm {n : Nat} {Γ : Ctx Head n} {C N a na b nb : Tm Head n} {u : Head}
    (hu : S.R.isUniverse u) (lN : Long S.R S.roles (.type Γ N)) (nC : NormalForm S.R S.roles Γ C N (.head u))
    (nA : NormalForm S.R S.roles Γ a na C) (nB : NormalForm S.R S.roles Γ b nb C)
    (universeType : TypeEq S.R Γ (.head u) (.head u)) :
    NormalForm S.R S.roles Γ (.id C a b) (.id N na nb) (.head u) := by
  have CN : TypeEq S.R Γ C N := ⟨u, hu, nC.2⟩
  have la := nA.1.convType S.levels CN
  have lb := nB.1.convType S.levels CN
  have tId : Typed S.R Γ (.id N na nb) (.head u) := .idForm nC.1.typed hu la.typed lb.typed
  exact ⟨.univ hu universeType tId (.id lN la lb ⟨u, hu, tId⟩), .idCong nC.2 hu nA.2 nB.2⟩

/-- **The normal form of a pair** at a dependent pair type is the pair of the normal forms. -/
theorem pair_normalForm {n : Nat} {Γ : Ctx Head n} {A a na b nb : Tm Head n} {B : Tm Head (n + 1)} {u v : Head}
    (tSigma : Typed S.R Γ (.sigma A B) (.head u)) (hu : S.R.isUniverse u)
    (family : Typed S.R (.snoc Γ A) B (.head v)) (hv : S.R.isUniverse v) (ta : Typed S.R Γ a A)
    (nA : NormalForm S.R S.roles Γ a na A) (nB : NormalForm S.R S.roles Γ b nb (inst0 a B)) :
    NormalForm S.R S.roles Γ (.pair a b) (.pair na nb) (.sigma A B) := by
  have fibres : TypeEq S.R Γ (inst0 a B) (inst0 na B) := TypeEq.of_instantiateEq family hv ta nA.2
  have lb := nB.1.convType S.levels fibres
  exact ⟨.pair (IsType.refl ⟨u, hu, tSigma⟩) (.pairIntro tSigma hu nA.1.typed lb.typed) nA.1 lb,
    .pairCong tSigma hu nA.2 nB.2⟩

end Normal

end ContextualDependentRank
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
