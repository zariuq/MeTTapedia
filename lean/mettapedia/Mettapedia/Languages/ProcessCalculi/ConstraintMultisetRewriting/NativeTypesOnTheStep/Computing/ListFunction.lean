import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DeclarationCheck
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Qualification
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerListAccumulators

/-!
# A list function in the definitional class: the list package is qualified

The tree's package of numbers and lists with their recursors, and two list functions whose recursive
call changes an accumulator (`rev-onto`, `dfa-run`, each admitted through its scrutinee-first form), is
**qualified** at every level (`lists_qualified`), with every hypothesis proved:

* its ten computation rules are exactly the instances of ten rows (`listPresentation`): the two rules of
  each recursor, the two rows of each scrutinee-first form, and the two definitions passing their
  arguments; the rows pass the syntactic declaration-time check (`list_check`), so they form a
  constructor system and conversion is Church–Rosser;
* the package's declaration records (typed right sides, structural recursion on the list) give root
  preservation and semantic constants; read in the algorithmic setting they give semantic constants for
  the algorithmic equality too (`listAlgorithmicConstants`), so conversion is decided.

A positive example: `rev-onto nil [0]` computes to `[0]` by three of the rows (`revOnto_example`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.ListFunction

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open AlgebraicSchema AlgebraicParallel ConversionCoherence
open ConstructorSystem (ConstructorPresentation)
open TowerNumbersModel (num zero succ numRec ctors u)
open TowerListAccumulatorsModel (list nil cons listRec step revOntoFirst revOnto runFirst run listCtors
  consFields revFirstEntries runFirstEntries revTele runTele revResult runResult revBody runBody revRhs
  runRhs computations)

variable (lv : LevelExpr Nat)

/-! ## The rows -/

/-- The ten rows of the package. -/
def listEquations : SchemaTable Tower.Head :=
  [⟨3, (.app (.app (.app (.app (.const numRec) (.var 2)) (.var 1)) (.var 0)) (.const zero), .var 1)⟩,
   ⟨4, (.app (.app (.app (.app (.const numRec) (.var 3)) (.var 2)) (.var 1)) (.app (.const succ) (.var 0)),
      .app (.app (.var 1) (.var 0)) (.app (.app (.app (.app (.const numRec) (.var 3)) (.var 2)) (.var 1))
        (.var 0)))⟩,
   ⟨3, (.app (.app (.app (.app (.const listRec) (.var 2)) (.var 1)) (.var 0)) (.const nil), .var 1)⟩,
   ⟨5, (.app (.app (.app (.app (.const listRec) (.var 4)) (.var 3)) (.var 2))
        (.app (.app (.const cons) (.var 1)) (.var 0)),
      .app (.app (.app (.var 2) (.var 1)) (.var 0))
        (.app (.app (.app (.app (.const listRec) (.var 4)) (.var 3)) (.var 2)) (.var 0)))⟩,
   ⟨1, (.app (.app (.const revOntoFirst) (.const nil)) (.var 0), .var 0)⟩,
   ⟨3, (.app (.app (.const revOntoFirst) (.app (.app (.const cons) (.var 2)) (.var 1))) (.var 0),
      .app (.app (.const revOntoFirst) (.var 1)) (.app (.app (.const cons) (.var 2)) (.var 0)))⟩,
   ⟨2, (.app (.app (.const revOnto) (.var 1)) (.var 0), .app (.app (.const revOntoFirst) (.var 0)) (.var 1))⟩,
   ⟨1, (.app (.app (.const runFirst) (.const nil)) (.var 0), .var 0)⟩,
   ⟨3, (.app (.app (.const runFirst) (.app (.app (.const cons) (.var 2)) (.var 1))) (.var 0),
      .app (.app (.const runFirst) (.var 1)) (.app (.app (.const step) (.var 0)) (.var 2)))⟩,
   ⟨2, (.app (.app (.const run) (.var 1)) (.var 0), .app (.app (.const runFirst) (.var 0)) (.var 1))⟩]

theorem listed (i : Nat) (h : i < listEquations.length) {arity : Nat} {left right : Tower.Tm arity}
    (same : listEquations[i] = ⟨arity, (left, right)⟩) : listEquations.family left right := by
  change (⟨arity, (left, right)⟩ : Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈ listEquations
  rw [← same]
  exact List.getElem_mem h

theorem step_of {entry : DeclName × RootComputation Tower.Head} (mem : entry ∈ computations)
    {n : Nat} {l r : Tower.Tm n} (h : entry.2.step l r) :
    (TowerListAccumulatorsModel.rules lv).computation.step l r :=
  RootComputation.step_unionAll (cs := computations) mem h

theorem computation_step {n : Nat} {l r : Tower.Tm n} :
    (TowerListAccumulatorsModel.rules lv).computation.step l r → ∃ entry ∈ computations, entry.2.step l r :=
  fun step => RootComputation.unionAll_step step

theorem mem₀ : (numRec, iotaComputation numRec ctors) ∈ computations := List.mem_cons_self ..
theorem mem₁ : (listRec, iotaComputation listRec listCtors) ∈ computations :=
  List.mem_cons_of_mem _ (List.mem_cons_self ..)

/-- **Every instance of a row is a step.** -/
theorem list_sound {arity n : Nat} {left right : Tower.Tm arity} (rule : listEquations.family left right)
    (σ : Sub Tower.Head arity n) :
    (TowerListAccumulatorsModel.rules lv).computation.step (subst σ left) (subst σ right) := by
  change (⟨arity, (left, right)⟩ : Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈ listEquations at rule
  simp only [listEquations, List.mem_cons, List.not_mem_nil, or_false] at rule
  rcases rule with same | same | same | same | same | same | same | same | same | same <;> cases same
  · exact step_of lv mem₀ ⟨σ 2, [σ 1, σ 0], 0, zero, [], [], σ 1, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact step_of lv mem₀
      ⟨σ 3, [σ 2, σ 1], 1, succ, [.recursive], [σ 0], σ 1, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact step_of lv mem₁ ⟨σ 2, [σ 1, σ 0], 0, nil, [], [], σ 1, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact step_of lv mem₁
      ⟨σ 4, [σ 3, σ 2], 1, cons, consFields, [σ 1, σ 0], σ 2, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact (TowerListAccumulatorsModel.declaresRevFirst lv fun _ => 0).rule
      TowerListAccumulatorsModel.mem_nil (consSub (σ 0) (consSub (.const nil) Fin.elim0)) [] rfl
  · exact (TowerListAccumulatorsModel.declaresRevFirst lv fun _ => 0).rule
      TowerListAccumulatorsModel.mem_cons (consSub (σ 0) (consSub (.const nil) Fin.elim0)) [σ 2, σ 1] rfl
  · exact (TowerListAccumulatorsModel.declaresRev lv fun _ => 0).rule σ
  · exact (TowerListAccumulatorsModel.declaresRunFirst lv fun _ => 0).rule
      TowerListAccumulatorsModel.mem_nil (consSub (σ 0) (consSub (.const nil) Fin.elim0)) [] rfl
  · exact (TowerListAccumulatorsModel.declaresRunFirst lv fun _ => 0).rule
      TowerListAccumulatorsModel.mem_cons (consSub (σ 0) (consSub (.const nil) Fin.elim0)) [σ 2, σ 1] rfl
  · exact (TowerListAccumulatorsModel.declaresRun lv fun _ => 0).rule σ

/-- **Every step is an instance of a row.** -/
theorem list_cover {n : Nat} {l r : Tower.Tm n}
    (step : (TowerListAccumulatorsModel.rules lv).computation.step l r) :
    ∃ (arity : Nat) (left right : Tower.Tm arity) (σ : Sub Tower.Head arity n),
      listEquations.family left right ∧ subst σ left = l ∧ subst σ right = r := by
  obtain ⟨entry, mem, h⟩ := computation_step lv step
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨p, ms, i, k, fields, args, m, hms, hi, has, hm, rfl, rfl⟩ := h
    rcases ms with _ | ⟨z, _ | ⟨s, _ | ⟨_, _⟩⟩⟩
    · cases hms
    · cases hms
    · rcases i with _ | _ | i
      · simp only [ctors, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        rcases args with _ | ⟨_, _⟩
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
          subst hm
          exact ⟨3, _, _, consSub s (consSub z (consSub p Fin.elim0)), listed 0 (by decide) rfl, rfl, rfl⟩
        · cases has
      · simp only [ctors, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        rcases args with _ | ⟨a, _ | ⟨_, _⟩⟩
        · cases has
        · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hm
          subst hm
          exact ⟨4, _, _, consSub a (consSub s (consSub z (consSub p Fin.elim0))), listed 1 (by decide) rfl,
            rfl, rfl⟩
        · cases has
      · cases hi
    · cases hms
  · obtain ⟨p, ms, i, k, fields, args, m, hms, hi, has, hm, rfl, rfl⟩ := h
    rcases ms with _ | ⟨b, _ | ⟨c, _ | ⟨_, _⟩⟩⟩
    · cases hms
    · cases hms
    · rcases i with _ | _ | i
      · simp only [listCtors, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        rcases args with _ | ⟨_, _⟩
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
          subst hm
          exact ⟨3, _, _, consSub c (consSub b (consSub p Fin.elim0)), listed 2 (by decide) rfl, rfl, rfl⟩
        · cases has
      · simp only [listCtors, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        rcases args with _ | ⟨x, _ | ⟨xs, _ | ⟨_, _⟩⟩⟩
        · cases has
        · cases has
        · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hm
          subst hm
          exact ⟨5, _, _, consSub xs (consSub x (consSub c (consSub b (consSub p Fin.elim0)))),
            listed 3 (by decide) rfl, rfl, rfl⟩
        · cases has
      · cases hi
    · cases hms
  · obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    simp only [listCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
    rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases as with _ | ⟨_, _⟩
      · exact ⟨1, _, _, fun _ => σ 0, listed 4 (by decide) rfl, rfl, rfl⟩
      · cases has
    · rcases as with _ | ⟨x, _ | ⟨xs, _ | ⟨_, _⟩⟩⟩
      · cases has
      · cases has
      · exact ⟨3, _, _, matchSub 0 2 [x, xs] (1 + 0) σ, listed 5 (by decide) rfl, rfl, rfl⟩
      · cases has
  · obtain ⟨σ, rfl, rfl⟩ := h
    exact ⟨2, _, _, σ, listed 6 (by decide) rfl, rfl, rfl⟩
  · obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    simp only [listCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
    rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases as with _ | ⟨_, _⟩
      · exact ⟨1, _, _, fun _ => σ 0, listed 7 (by decide) rfl, rfl, rfl⟩
      · cases has
    · rcases as with _ | ⟨a, _ | ⟨w, _ | ⟨_, _⟩⟩⟩
      · cases has
      · cases has
      · exact ⟨3, _, _, matchSub 0 2 [a, w] (1 + 0) σ, listed 8 (by decide) rfl, rfl, rfl⟩
      · cases has
  · obtain ⟨σ, rfl, rfl⟩ := h
    exact ⟨2, _, _, σ, listed 9 (by decide) rfl, rfl, rfl⟩

/-- **The package's computation, presented by its rows.** -/
def listPresentation : SchemaPresentation (TowerListAccumulatorsModel.rules lv) where
  schema := listEquations.family
  sound := list_sound lv
  cover := list_cover lv

/-- **A positive example**: `rev-onto nil [0]` computes to `[0]`. -/
theorem revOnto_example :
    StepStar (TowerListAccumulatorsModel.rules lv)
      (.app (.app (.const revOnto) (.const nil)) (.app (.app (.const cons) (.const zero)) (.const nil)) :
        Tower.Tm 0)
      (.app (.app (.const cons) (.const zero)) (.const nil)) :=
  .head (.root (list_sound lv (listed 6 (by decide) rfl)
      (consSub (.app (.app (.const cons) (.const zero)) (.const nil)) (consSub (.const nil) Fin.elim0))))
    (.head (.root (list_sound lv (listed 5 (by decide) rfl)
        (consSub (.const nil) (consSub (.const nil) (consSub (.const zero) Fin.elim0)))))
      (.single (.root (list_sound lv (listed 4 (by decide) rfl)
        (consSub (.app (.app (.const cons) (.const zero)) (.const nil)) Fin.elim0)))))

/-! ## The rows pass the syntactic check -/

def listDefined (name : DeclName) : Bool :=
  name == numRec || name == listRec || name == revOntoFirst || name == revOnto || name == runFirst ||
    name == run

def listArity (name : DeclName) : Nat :=
  if name == numRec || name == listRec then 4 else 2

theorem list_check : DeclarationCheck.checkTable listDefined listArity listEquations = true := by
  decide

/-- **The list package as a definition by constructor patterns.** -/
def listConstructors : ConstructorPresentation (TowerListAccumulatorsModel.rules lv) where
  presentation := listPresentation lv
  system := DeclarationCheck.checkedSystem list_check
  same _ _ := Iff.rfl
  symmetric := LevelTower.headEq_symmetric

/-! ## Semantic constants for the algorithmic equality -/

section Algorithmic

open TowerListAccumulatorsModel

variable (valuation : Nat → Nat)

abbrev algSetting : Setting Tower.Head ℕ := algorithmicSetting (setting lv valuation)

theorem lawsA : (algSetting lv valuation).E.Laws (algSetting lv valuation).R (algSetting lv valuation).roles :=
  algorithmicSetting_laws (S := setting lv valuation) (laws lv valuation) (constants lv valuation) (roots lv)
    (heads lv) (algebra lv)

theorem declaresNumA :
    DeclaresInductive (algSetting lv valuation) (constantFreeRules (TowerListAccumulatorsModel.rules lv))
      TowerNumbersModel.rules₁ TowerNumbersModel.rules₂ num u ctors numRec (.sort lv) :=
  have d := declaresNum lv valuation
  { role := d.role, recRole := d.recRole, hu := d.hu, hv := d.hv, sub₀ := d.sub₀, sub₁ := d.sub₁,
    sub₂ := d.sub₂, semantic₀ := (fun declared => nomatch declared), stage₁ := d.stage₁, stage₂ := d.stage₂,
    declared := d.declared, ctorDeclared := d.ctorDeclared, recDeclared := d.recDeclared,
    fieldTyped := d.fieldTyped, ctorTyped := d.ctorTyped, recTyped := d.recTyped, iota := d.iota }

theorem declaresListA :
    DeclaresInductive (algSetting lv valuation) TowerNumbersModel.rules₂ listStage₁ listStage₂ list u
      listCtors listRec (.sort lv) :=
  have d := declaresList lv valuation
  { role := d.role, recRole := d.recRole, hu := d.hu, hv := d.hv, sub₀ := d.sub₀, sub₁ := d.sub₁,
    sub₂ := d.sub₂, semantic₀ := (declaresNumA lv valuation).semantic₂ (lawsA lv valuation),
    stage₁ := d.stage₁, stage₂ := d.stage₂, declared := d.declared, ctorDeclared := d.ctorDeclared,
    recDeclared := d.recDeclared, fieldTyped := d.fieldTyped, ctorTyped := d.ctorTyped,
    recTyped := d.recTyped, iota := d.iota }

theorem semantic_bodyA : AllSemantic (algSetting lv valuation) bodyStage := by
  intro name type declared
  change (if name = step then some stepType else listStage₂.constantType name) = some type at declared
  split at declared
  · rename_i h
    subst h
    cases declared
    obtain ⟨w, hw, t⟩ := arrowType_typed (R := bodyStage) num_typedB num_typedB num_typedB
      (.sort _) (fun _ _ => .sorts _ _) (fun _ => .sort _)
    exact SemanticConstant.rigid (S := algSetting lv valuation) (lawsA lv valuation) (name := step) rfl
      (Derivable.mono (sub_body lv) t) hw roles_step
  · exact (declaresListA lv valuation).semantic₂ (lawsA lv valuation) declared

theorem semantic_stageA : AllSemantic (algSetting lv valuation) (stageRules lv) := by
  intro name type declared
  change (if name = listRec then some (recType list (.sort lv) listCtors)
    else if name = numRec then some (recType num (.sort lv) ctors)
    else bodyStage.constantType name) = some type at declared
  split at declared
  · rename_i h
    subst h
    cases declared
    intro m Δ formed P r
    exact (declaresListA lv valuation).rec_semantic (lawsA lv valuation) formed r
  · split at declared
    · rename_i _ h
      subst h
      cases declared
      intro m Δ formed P r
      exact (declaresNumA lv valuation).rec_semantic (lawsA lv valuation) formed r
    · exact semantic_bodyA lv valuation declared

theorem declaresRevFirstA :
    DeclaresRecursion (algSetting lv valuation) (stageRules lv) revOntoFirst list listCtors
      revFirstEntries 0 (1 + 0) (Presentation.rename (teleMove 1 0) revResult) revBody :=
  have d := declaresRevFirst lv valuation
  { role := d.role, scrutinee := d.scrutinee, declared := d.declared, sub₀ := d.sub₀,
    semantic₀ := semantic_stageA lv valuation, typed := d.typed, formed := d.formed,
    bodyTyped := d.bodyTyped, rule := d.rule }

theorem declaresRunFirstA :
    DeclaresRecursion (algSetting lv valuation) (stageRules lv) runFirst list listCtors runFirstEntries
      0 (1 + 0) (Presentation.rename (teleMove 1 0) runResult) runBody :=
  have d := declaresRunFirst lv valuation
  { role := d.role, scrutinee := d.scrutinee, declared := d.declared, sub₀ := d.sub₀,
    semantic₀ := semantic_stageA lv valuation, typed := d.typed, formed := d.formed,
    bodyTyped := d.bodyTyped, rule := d.rule }

theorem semantic_defA : AllSemantic (algSetting lv valuation) defStage := by
  intro name type declared
  change (if name = revOntoFirst then some revFirstType
    else if name = runFirst then some runFirstType
    else bodyStage.constantType name) = some type at declared
  split at declared
  · rename_i h
    subst h
    cases declared
    exact (declaresRevFirstA lv valuation).semantic (lawsA lv valuation) (declaresListA lv valuation)
  · split at declared
    · rename_i _ h
      subst h
      cases declared
      exact (declaresRunFirstA lv valuation).semantic (lawsA lv valuation) (declaresListA lv valuation)
    · exact semantic_bodyA lv valuation declared

theorem declaresRevA :
    DeclaresDefinition (algSetting lv valuation) defStage revOnto revTele revResult revRhs :=
  have d := declaresRev lv valuation
  { role := d.role, declared := d.declared, sub₀ := d.sub₀, semantic₀ := semantic_defA lv valuation,
    typed := d.typed, body := d.body, rule := d.rule }

theorem declaresRunA :
    DeclaresDefinition (algSetting lv valuation) defStage run runTele runResult runRhs :=
  have d := declaresRun lv valuation
  { role := d.role, declared := d.declared, sub₀ := d.sub₀, semantic₀ := semantic_defA lv valuation,
    typed := d.typed, body := d.body, rule := d.rule }

/-- **Every constant of the list package is semantic for the algorithmic equality.** -/
theorem listAlgorithmicConstants : SemanticConstants (algSetting lv valuation) := by
  intro name type w declared _ _
  change (if name = revOnto then some revType
    else if name = run then some runType
    else if name = listRec then some (recType list (.sort lv) listCtors)
    else if name = numRec then some (recType num (.sort lv) ctors)
    else defStage.constantType name) = some type at declared
  split at declared
  · rename_i h
    subst h
    cases declared
    exact (declaresRevA lv valuation).semantic (lawsA lv valuation)
  · split at declared
    · rename_i _ h
      subst h
      cases declared
      exact (declaresRunA lv valuation).semantic (lawsA lv valuation)
    · split at declared
      · rename_i _ _ h
        subst h
        cases declared
        intro m Δ formed P r
        exact (declaresListA lv valuation).rec_semantic (lawsA lv valuation) formed r
      · split at declared
        · rename_i _ _ _ h
          subst h
          cases declared
          intro m Δ formed P r
          exact (declaresNumA lv valuation).rec_semantic (lawsA lv valuation) formed r
        · exact semantic_defA lv valuation declared

end Algorithmic

/-- Head equality of the list package is decided. -/
theorem listDecideHeads (h h' : Tower.Head) :
    HeadSame (TowerListAccumulatorsModel.rules lv) h h' ∨ ¬ HeadSame (TowerListAccumulatorsModel.rules lv) h h' := by
  rcases Decidable.em (Tower.HeadEq h h') with same | different
  · exact .inl (.inr same)
  · rcases Decidable.em (h = h') with equal | unequal
    · exact .inl (.inl equal)
    · exact .inr fun same => same.elim unequal different

/-- **The list package is qualified, at every level**: `rev-onto` and `dfa-run`, list functions by
structural recursion with a changing accumulator. -/
theorem lists_qualified : Qualified (TowerListAccumulatorsModel.setting lv fun _ => 0) where
  laws := TowerListAccumulatorsModel.laws lv _
  constructors := ⟨listConstructors lv⟩
  constants := TowerListAccumulatorsModel.constants lv _
  roots := TowerListAccumulatorsModel.roots lv
  heads := TowerListAccumulatorsModel.heads lv
  algebra := TowerListAccumulatorsModel.algebra lv
  algorithmicConstants := listAlgorithmicConstants lv _
  decideHeads := listDecideHeads lv

end NativeTypesOnTheStep.Computing.ListFunction

#print axioms NativeTypesOnTheStep.Computing.ListFunction.list_sound
#print axioms NativeTypesOnTheStep.Computing.ListFunction.list_cover
#print axioms NativeTypesOnTheStep.Computing.ListFunction.listPresentation
#print axioms NativeTypesOnTheStep.Computing.ListFunction.revOnto_example
#print axioms NativeTypesOnTheStep.Computing.ListFunction.list_check
#print axioms NativeTypesOnTheStep.Computing.ListFunction.listConstructors
#print axioms NativeTypesOnTheStep.Computing.ListFunction.listAlgorithmicConstants
#print axioms NativeTypesOnTheStep.Computing.ListFunction.lists_qualified

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
