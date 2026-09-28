import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Package
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstructorSystemDevelopment

/-!
# Confluence of the certified-transform program

Every equation of the program is a definition by constructor patterns, except
identity elimination: the draft fires `id:eliminate A x P d y e` when `e`
computes to reflexivity at the point and the endpoint is the point, a
comparison of three arguments.  As a rewrite rule that is non-left-linear.

Separating the repeated point gives the rule `id:eliminate A x P d y
(refl z) → d`.  The program with that rule is a constructor system:
decoders of the proof family, the equations of `add` and `pow`, and the
package.  It is therefore Church–Rosser, and its conversion separates
dependent products and pairs componentwise.  Every step of the draft's
program is a step of this linearized program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Confluence

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Presentation.Declaration Presentation.FormationSensitive
open Presentation.AlgebraicSchema (SchemaTable SchemaFamily SchemaStep LeftLinear variableMultiplicity)
open Presentation.AlgebraicParallel Presentation.ConversionCoherence
open Presentation.ConstructorSystem (Pattern LeftSide System)
open SetProfile (baseName constantName numTy zeroNative sucNative addNative
  eqNumNative holdsName targetRules)
open CertifiedTransformProgram.Package
open Mettapedia.Logic

/-! ## The linearized program -/

/-- Identity elimination at reflexivity, with the repeated point separated:
`id:eliminate A x P d y (refl z) = d`. -/
abbrev jIotaLinear : Σ arity : Nat, Tower.Tm arity × Tower.Tm arity :=
  ⟨6, (jApp (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.refl (.var 0)), .var 2)⟩

def linearEquations : SchemaTable Tower.Head :=
  [jIotaLinear, numRecZeroEquation, numRecSucEquation, eqAtEquation, sucMoveEquation, keepEquation,
   transportEquation, composeEquation, iterZeroEquation, iterSucEquation, returnIterEquation,
   sucStepEquation, holdsAtEquation, holdsMoveEquation, holdsStepEquation]

def linearDeclarations : Signature Tower.Head where
  entries := packageDeclarations.entries
  computation := SchemaFamily.computation linearEquations.family

noncomputable abbrev linearRules : Rules Tower.Head := extendRules targetRules linearDeclarations

/-- Every step of the program is a step of the linearized program. -/
theorem packageToLinear : packageRules.Morphism linearRules (fun head => head) where
  headTyping := fun typing => typing
  isUniverse := fun isU => isU
  join := fun joined => joined
  cumulative := fun order => order
  headEq := fun equality => equality
  constantType := by
    intro name type known
    simp only [Tm.mapHead_id]
    exact known
  computation := by
    intro n left right step
    simp only [Tm.mapHead_id]
    cases step with
    | inherited inner => exact .inherited inner
    | delta unfolding => exact .delta unfolding
    | declared declared =>
        cases declared with
        | instantiate listed substitution =>
            simp only [SchemaTable.family, packageEquations, List.mem_cons, List.not_mem_nil,
              or_false] at listed
            rcases listed with same | same | same | same | same | same | same | same | same |
              same | same | same | same | same | same
            · cases same
              exact .declared (SchemaTable.step_of_mem linearEquations
                (List.getElem_mem (l := linearEquations) (n := 0) (by decide))
                (Fin.cons (substitution 2) (Fin.cons (substitution 2)
                  (Fin.cons (substitution 0) (Fin.cons (substitution 1)
                    (Fin.cons (substitution 2) (Fin.cons (substitution 3) Fin.elim0)))))))
            all_goals
              cases same
              exact .declared (SchemaTable.step_of_mem linearEquations
                (by simp [linearEquations]) substitution)


/-! ## The rewrite system -/

/-- `Holds (imp p q) ↦ Holds p → Holds q`, over the telescope `p, q`. -/
abbrev implicationLeft : Tower.Tm 2 :=
  .app (.const holdsName) (.app (.app (.const SetProfile.impName) (.var 1)) (.var 0))

abbrev implicationRight : Tower.Tm 2 :=
  FormationSensitiveHOLGenericProofFamily.implicationFamily holdsName (.var 1) (.var 0)

/-- `Holds (all@T P) ↦ Π x : T. Holds (P x)`. -/
abbrev universalLeft (type : HOL.Ty SetProfile.SetBase) : Tower.Tm 1 :=
  .app (.const holdsName) (.app (.const (SetProfile.allName type)) (.var 0))

noncomputable abbrev universalRight (type : HOL.Ty SetProfile.SetBase) : Tower.Tm 1 :=
  FormationSensitiveHOLGenericProofFamily.universalFamily SetProfile.signature holdsName
    type (.var 0)

/-- The equations of the linearized program: both decoders of the proof family,
the equations of `add` and `pow`, and the package with separated identity
elimination. -/
inductive LinearSchema : SchemaFamily Tower.Head
  | implication : LinearSchema implicationLeft implicationRight
  | universal (type : HOL.Ty SetProfile.SetBase) :
      LinearSchema (universalLeft type) (universalRight type)
  | native {arity : Nat} {left right : Tower.Tm arity} :
      (⟨arity, (left, right)⟩ : Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈
        SetProfile.nativeEquations → LinearSchema left right
  | package {arity : Nat} {left right : Tower.Tm arity} :
      (⟨arity, (left, right)⟩ : Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈
        linearEquations → LinearSchema left right

theorem implication_instance {n : Nat} (substitution : Sub Tower.Head 2 n) :
    subst substitution implicationRight =
      FormationSensitiveHOLGenericProofFamily.implicationFamily holdsName
        (substitution 1) (substitution 0) := by
  simp only [implicationRight, FormationSensitiveHOLGenericProofFamily.implicationFamily_subst]
  rfl

theorem universal_instance {n : Nat} (type : HOL.Ty SetProfile.SetBase)
    (substitution : Sub Tower.Head 1 n) :
    subst substitution (universalRight type) =
      FormationSensitiveHOLGenericProofFamily.universalFamily SetProfile.signature holdsName
        type (substitution 0) := by
  simp only [universalRight, FormationSensitiveHOLGenericProofFamily.universalFamily_subst]
  rfl

theorem linearSchema_sound {arity n : Nat} {left right : Tower.Tm arity}
    (rule : LinearSchema left right) (substitution : Sub Tower.Head arity n) :
    linearRules.computation.step (subst substitution left) (subst substitution right) := by
  cases rule with
  | implication =>
      rw [implication_instance]
      exact RootStep.inherited (RootStep.inherited (RootStep.declared
        (FormationSensitiveHOLGenericProofFamily.DecoderStep.implication
          (substitution 1) (substitution 0))))
  | universal type =>
      rw [universal_instance]
      exact RootStep.inherited (RootStep.inherited (RootStep.declared
        (FormationSensitiveHOLGenericProofFamily.DecoderStep.universal type (substitution 0))))
  | native listed =>
      exact RootStep.inherited (RootStep.inherited (RootStep.inherited (RootStep.declared
        (SchemaTable.step_of_mem SetProfile.nativeEquations listed substitution))))
  | package listed =>
      exact RootStep.declared (SchemaTable.step_of_mem linearEquations listed substitution)

theorem valueOf_ofList_none (declarations : List (DeclName × Entry Tower.Head))
    (noValues : ∀ declaration ∈ declarations, declaration.2.value? = none) (name : DeclName) :
    ((Signature.ofList declarations).entries name).bind Entry.value? = none := by
  induction declarations with
  | nil => rfl
  | cons declaration rest ih =>
      change (if name = declaration.1 then some declaration.2
        else (Signature.ofList rest).entries name).bind Entry.value? = none
      split
      · exact noValues declaration (List.mem_cons_self ..)
      · exact ih (fun other listed => noValues other (List.mem_cons_of_mem _ listed))

theorem bind_value_ite {condition : Prop} [Decidable condition]
    {first second : Option (Entry Tower.Head)}
    (firstNone : first.bind Entry.value? = none) (secondNone : second.bind Entry.value? = none) :
    (if condition then first else second).bind Entry.value? = none := by
  split <;> assumption

theorem fixedEntry_noValue (name : DeclName) :
    (SetProfile.fixedEntry name).bind Entry.value? = none := by
  unfold SetProfile.fixedEntry
  repeat' (first | rfl | apply bind_value_ite)

theorem profile_valueOf (name : DeclName) :
    SetProfile.signature.declarations.valueOf? name = none := by
  change (SetProfile.entries name).bind Entry.value? = none
  unfold SetProfile.entries
  split
  · rfl
  · split
    · rfl
    · exact fixedEntry_noValue name

theorem family_valueOf (name : DeclName) :
    (FormationSensitiveHOLGenericProofFamily.declarations SetProfile.signature
      holdsName).valueOf? name = none := by
  simp only [Signature.valueOf?, FormationSensitiveHOLGenericProofFamily.declarations,
    Signature.insert, Signature.empty]
  split <;> rfl

theorem assumption_valueOf (name : DeclName) :
    SetProfile.assumptionDeclarations.valueOf? name = none := by
  unfold SetProfile.assumptionDeclarations Signature.valueOf?
  refine valueOf_ofList_none _ ?_ name
  intro declaration listed
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl <;> rfl

theorem linear_valueOf (name : DeclName) : linearDeclarations.valueOf? name = none := by
  unfold linearDeclarations packageDeclarations Signature.valueOf?
  dsimp only
  refine valueOf_ofList_none _ ?_ name
  intro declaration listed
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

/-- Every root step of the linearized program is an instance of its equations. -/
theorem linearSchema_cover {n : Nat} {source target : Tower.Tm n}
    (step : linearRules.computation.step source target) :
    ∃ (arity : Nat) (left right : Tower.Tm arity) (substitution : Sub Tower.Head arity n),
      LinearSchema left right ∧ subst substitution left = source ∧
        subst substitution right = target := by
  cases step with
  | inherited targetStep =>
      cases targetStep with
      | inherited proofStep =>
          cases proofStep with
          | inherited profileStep =>
              cases profileStep with
              | inherited towerStep => exact towerStep.elim
              | delta unfolding => rw [profile_valueOf] at unfolding; cases unfolding
              | declared declared =>
                  cases declared with
                  | instantiate listed substitution =>
                      exact ⟨_, _, _, substitution, .native listed, rfl, rfl⟩
          | delta unfolding => rw [family_valueOf] at unfolding; cases unfolding
          | declared decoder =>
              cases decoder with
              | implication p q =>
                  exact ⟨2, implicationLeft, implicationRight, Fin.cons q (Fin.cons p Fin.elim0),
                    .implication, rfl, by rw [implication_instance]; rfl⟩
              | universal type predicate =>
                  exact ⟨1, universalLeft type, universalRight type, Fin.cons predicate Fin.elim0,
                    .universal type, rfl, by rw [universal_instance]; rfl⟩
      | delta unfolding => rw [assumption_valueOf] at unfolding; cases unfolding
      | declared declared =>
          change (Signature.ofList _).computation.step _ _ at declared
          rw [Signature.computation_ofList] at declared
          exact declared.elim
  | delta unfolding => rw [linear_valueOf] at unfolding; cases unfolding
  | declared declared =>
      cases declared with
      | instantiate listed substitution =>
          exact ⟨_, _, _, substitution, .package listed, rfl, rfl⟩

def linearPresentation : SchemaPresentation linearRules where
  schema := LinearSchema
  sound := linearSchema_sound
  cover := by
    intro n source target step
    obtain ⟨arity, left, right, substitution, rule, leftShape, rightShape⟩ :=
      linearSchema_cover step
    exact ⟨arity, left, right, substitution, rule, leftShape, rightShape⟩

/-! ## A constructor system -/

/-- The defined constants: the proof family, `add`, `pow`, and the package. -/
def definedHeads : List DeclName :=
  [holdsName, constantName .add, constantName .pow, jName, numRecName, eqAtName, sucMoveName,
   keepName, transportName, composeName, iterName, returnIterName, sucStepName, holdsAtName,
   holdsMoveName, holdsStepName]

def Defined (name : DeclName) : Prop := name ∈ definedHeads

instance : DecidablePred Defined := fun name => inferInstanceAs (Decidable (name ∈ definedHeads))

def arities : List (DeclName × Nat) :=
  [(holdsName, 1), (constantName .add, 2), (constantName .pow, 2), (jName, 6), (numRecName, 4),
   (eqAtName, 1), (sucMoveName, 2), (keepName, 4), (transportName, 6), (composeName, 6),
   (iterName, 6), (returnIterName, 1), (sucStepName, 2), (holdsAtName, 1), (holdsMoveName, 2),
   (holdsStepName, 2)]

def arityOf (name : DeclName) : Nat :=
  ((arities.find? (fun entry => entry.1 == name)).map Prod.snd).getD 0

/-- No quantifier instance is a defined constant. -/
theorem allName_not_defined (type : HOL.Ty SetProfile.SetBase) :
    ¬ Defined (SetProfile.allName type) := by
  intro listed
  simp only [Defined, definedHeads, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with same | same | same | same | same | same | same | same | same | same |
    same | same | same | same | same | same <;>
    exact SetProfile.allName_ne_of_allInstance? (by decide) type same

macro "left_side" : tactic =>
  `(tactic| repeat' (first
    | exact LeftSide.const _
    | exact Pattern.var _
    | (apply Pattern.const; decide)
    | apply LeftSide.app
    | apply Pattern.app
    | apply Pattern.refl))

theorem linearSchema_left {m : Nat} {left right : Tower.Tm m} (rule : LinearSchema left right) :
    ∃ name, Defined name ∧ 0 < arityOf name ∧ LeftSide Defined left name (arityOf name) := by
  cases rule with
  | implication =>
      refine ⟨holdsName, by decide, by decide, ?_⟩
      show LeftSide Defined implicationLeft holdsName 1
      left_side
  | universal type =>
      refine ⟨holdsName, by decide, by decide, ?_⟩
      show LeftSide Defined (universalLeft type) holdsName 1
      exact .app (.const _) (.app (.const (allName_not_defined type)) (.var 0))
  | native listed =>
      simp only [SetProfile.nativeEquations, List.mem_cons, List.not_mem_nil,
        or_false] at listed
      rcases listed with same | same | same | same
      · cases same
        exact ⟨constantName .add, by decide, by decide, by
          show LeftSide Defined _ (constantName .add) 2
          left_side⟩
      · cases same
        exact ⟨constantName .add, by decide, by decide, by
          show LeftSide Defined _ (constantName .add) 2
          left_side⟩
      · cases same
        exact ⟨constantName .pow, by decide, by decide, by
          show LeftSide Defined _ (constantName .pow) 2
          left_side⟩
      · cases same
        exact ⟨constantName .pow, by decide, by decide, by
          show LeftSide Defined _ (constantName .pow) 2
          left_side⟩
  | package listed =>
      simp only [linearEquations, List.mem_cons, List.not_mem_nil, or_false] at listed
      rcases listed with same | same | same | same | same | same | same | same | same | same |
        same | same | same | same | same
      · cases same
        exact ⟨jName, by decide, by decide, by
          show LeftSide Defined _ (jName) 6
          left_side⟩
      · cases same
        exact ⟨numRecName, by decide, by decide, by
          show LeftSide Defined _ (numRecName) 4
          left_side⟩
      · cases same
        exact ⟨numRecName, by decide, by decide, by
          show LeftSide Defined _ (numRecName) 4
          left_side⟩
      · cases same
        exact ⟨eqAtName, by decide, by decide, by
          show LeftSide Defined _ (eqAtName) 1
          left_side⟩
      · cases same
        exact ⟨sucMoveName, by decide, by decide, by
          show LeftSide Defined _ (sucMoveName) 2
          left_side⟩
      · cases same
        exact ⟨keepName, by decide, by decide, by
          show LeftSide Defined _ (keepName) 4
          left_side⟩
      · cases same
        exact ⟨transportName, by decide, by decide, by
          show LeftSide Defined _ (transportName) 6
          left_side⟩
      · cases same
        exact ⟨composeName, by decide, by decide, by
          show LeftSide Defined _ (composeName) 6
          left_side⟩
      · cases same
        exact ⟨iterName, by decide, by decide, by
          show LeftSide Defined _ (iterName) 6
          left_side⟩
      · cases same
        exact ⟨iterName, by decide, by decide, by
          show LeftSide Defined _ (iterName) 6
          left_side⟩
      · cases same
        exact ⟨returnIterName, by decide, by decide, by
          show LeftSide Defined _ (returnIterName) 1
          left_side⟩
      · cases same
        exact ⟨sucStepName, by decide, by decide, by
          show LeftSide Defined _ (sucStepName) 2
          left_side⟩
      · cases same
        exact ⟨holdsAtName, by decide, by decide, by
          show LeftSide Defined _ (holdsAtName) 1
          left_side⟩
      · cases same
        exact ⟨holdsMoveName, by decide, by decide, by
          show LeftSide Defined _ (holdsMoveName) 2
          left_side⟩
      · cases same
        exact ⟨holdsStepName, by decide, by decide, by
          show LeftSide Defined _ (holdsStepName) 2
          left_side⟩

theorem linearSchema_linear : AlgebraicSchema.LeftLinearFamily LinearSchema := by
  intro m left right rule
  cases rule with
  | implication => unfold LeftLinear; decide
  | universal type => exact Fin.forall_fin_one.mpr (by simp [variableMultiplicity])
  | native listed =>
      simp only [SetProfile.nativeEquations, List.mem_cons, List.not_mem_nil,
        or_false] at listed
      rcases listed with same | same | same | same <;> cases same <;> (unfold LeftLinear; decide)
  | package listed =>
      simp only [linearEquations, List.mem_cons, List.not_mem_nil, or_false] at listed
      rcases listed with same | same | same | same | same | same | same | same | same | same |
        same | same | same | same | same <;> cases same <;> (unfold LeftLinear; decide)

theorem linearSchema_covered {m : Nat} {left right : Tower.Tm m} (rule : LinearSchema left right) :
    ∀ index, 0 < variableMultiplicity index right → 0 < variableMultiplicity index left := by
  cases rule with
  | implication => decide
  | universal type => exact Fin.forall_fin_one.mpr fun _ => Nat.zero_lt_one
  | native listed =>
      simp only [SetProfile.nativeEquations, List.mem_cons, List.not_mem_nil,
        or_false] at listed
      rcases listed with same | same | same | same <;> cases same <;> decide
  | package listed =>
      simp only [linearEquations, List.mem_cons, List.not_mem_nil, or_false] at listed
      rcases listed with same | same | same | same | same | same | same | same | same | same |
        same | same | same | same | same <;> cases same <;> decide

open Presentation.ConstructorSystem (unifiable)

theorem native_disjoint : ∀ first ∈ SetProfile.nativeEquations,
    ∀ second ∈ SetProfile.nativeEquations,
      unifiable first.2.1 second.2.1 = true → first = second := by decide

theorem package_disjoint : ∀ first ∈ linearEquations, ∀ second ∈ linearEquations,
    unifiable first.2.1 second.2.1 = true → first = second := by decide

theorem native_package_apart : ∀ first ∈ SetProfile.nativeEquations,
    ∀ second ∈ linearEquations,
      unifiable first.2.1 second.2.1 = false ∧ unifiable second.2.1 first.2.1 = false := by decide

theorem implication_apart : (∀ equation ∈ SetProfile.nativeEquations,
    unifiable implicationLeft equation.2.1 = false ∧ unifiable equation.2.1 implicationLeft = false) ∧
    (∀ equation ∈ linearEquations,
      unifiable implicationLeft equation.2.1 = false ∧ unifiable equation.2.1 implicationLeft = false) := by
  decide

theorem universal_apart (type : HOL.Ty SetProfile.SetBase) :
    (∀ equation ∈ SetProfile.nativeEquations,
      unifiable (universalLeft type) equation.2.1 = false ∧
        unifiable equation.2.1 (universalLeft type) = false) ∧
    (∀ equation ∈ linearEquations,
      unifiable (universalLeft type) equation.2.1 = false ∧
        unifiable equation.2.1 (universalLeft type) = false) ∧
    unifiable implicationLeft (universalLeft type) = false ∧
    unifiable (universalLeft type) implicationLeft = false := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · intro equation listed
    simp only [SetProfile.nativeEquations, List.mem_cons, List.not_mem_nil,
      or_false] at listed
    rcases listed with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
  · intro equation listed
    simp only [linearEquations, List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem universal_universal (type type' : HOL.Ty SetProfile.SetBase)
    (meet : unifiable (universalLeft type) (universalLeft type') = true) : type = type' := by
  simp only [unifiable, decide_eq_true_eq, Bool.and_eq_true, Bool.and_true] at meet
  exact SetProfile.allName_injective meet.2

theorem linearSchema_disjoint {m m' : Nat} {left right : Tower.Tm m} {left' right' : Tower.Tm m'}
    (rule : LinearSchema left right) (rule' : LinearSchema left' right')
    (meet : unifiable left left' = true) :
    (⟨m, (left, right)⟩ : Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) = ⟨m', (left', right')⟩ := by
  cases rule with
  | implication =>
      cases rule' with
      | implication => rfl
      | universal type => rw [(universal_apart type).2.2.1] at meet; cases meet
      | native listed => rw [(implication_apart.1 _ listed).1] at meet; cases meet
      | package listed => rw [(implication_apart.2 _ listed).1] at meet; cases meet
  | universal type =>
      cases rule' with
      | implication => rw [(universal_apart type).2.2.2] at meet; cases meet
      | universal type' => obtain rfl := universal_universal type type' meet; rfl
      | native listed => rw [((universal_apart type).1 _ listed).1] at meet; cases meet
      | package listed => rw [((universal_apart type).2.1 _ listed).1] at meet; cases meet
  | native listed =>
      cases rule' with
      | implication => rw [(implication_apart.1 _ listed).2] at meet; cases meet
      | universal type => rw [((universal_apart type).1 _ listed).2] at meet; cases meet
      | native listed' => exact native_disjoint _ listed _ listed' meet
      | package listed' => rw [(native_package_apart _ listed _ listed').1] at meet; cases meet
  | package listed =>
      cases rule' with
      | implication => rw [(implication_apart.2 _ listed).2] at meet; cases meet
      | universal type => rw [((universal_apart type).2.1 _ listed).2] at meet; cases meet
      | native listed' => rw [(native_package_apart _ listed' _ listed).2] at meet; cases meet
      | package listed' => exact package_disjoint _ listed _ listed' meet

/-- The linearized program as a constructor system. -/
noncomputable def linearSystem : System Tower.Head where
  schema := LinearSchema
  defined := Defined
  arity := arityOf
  left := linearSchema_left
  linear := linearSchema_linear
  covered := linearSchema_covered
  determined := Presentation.ConstructorSystem.determined_of_disjoint
    (fun rule => by
      obtain ⟨name, _, _, side⟩ := linearSchema_left rule
      exact ⟨name, _, side⟩)
    linearSchema_covered linearSchema_disjoint

/-! ## Church–Rosser and the conversion boundaries -/

/-- The linearized program as a definition by constructor patterns. -/
noncomputable def linearConstructors :
    Presentation.ConstructorSystem.ConstructorPresentation linearRules where
  presentation := linearPresentation
  system := linearSystem
  same := fun _ _ => Iff.rfl
  symmetric := Tower.headEq_symmetric

/-- The linearized program's conversion is Church–Rosser. -/
theorem churchRosser : ChurchRosser linearRules := linearConstructors.churchRosser

theorem piConversionBoundary : PiConversionBoundary linearRules :=
  linearConstructors.piConversionBoundary

theorem sigmaConversionBoundary : SigmaConversionBoundary linearRules :=
  linearConstructors.sigmaConversionBoundary

/-! ## Axiom audit -/

#print axioms packageToLinear
#print axioms linearSchema_cover
#print axioms linearSchema_disjoint
#print axioms churchRosser
#print axioms piConversionBoundary
#print axioms sigmaConversionBoundary

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Confluence
