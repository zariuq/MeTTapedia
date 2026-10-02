import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.Model

/-!
# The executable package as equations of the program

The root computation of the executable package is exactly the instances of
sixteen equations: the equations of `add` and `pow`, and the program's equations for
identity elimination with the repeated point separated, the recursor, the
definitions and the iterator. Every step of a declared computation is an
instance of one equation, and every instance of an equation is a step.

The equations are left-linear definitions by constructor patterns whose left
sides do not overlap, so the package's conversion is Church–Rosser. Then two
typed terms that are convertible are equal in the typed equality, and every
formation-sensitive typing derivation of the package is a typing derivation of
the typed equality.

The equations are equations of the linearized program and the package's declared
types are the program's, so the package is a sub-package of the linearized
program: its typing derivations and steps are the program's.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Presentation.Declaration
open Presentation.AlgebraicSchema (SchemaTable SchemaFamily LeftLinear variableMultiplicity)
open Presentation.AlgebraicParallel Presentation.ConversionCoherence
open Presentation.ConstructorSystem (Pattern LeftSide System ConstructorPresentation unifiable)
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open TelescopeAbstraction (applyClosed)
open Package (jName numRecName eqAtName sucMoveName keepName transportName composeName
  iterName returnIterName sucStepName numRecZeroEquation numRecSucEquation eqAtEquation
  sucMoveEquation keepEquation transportEquation composeEquation iterZeroEquation iterSucEquation
  returnIterEquation sucStepEquation)
open Confluence (jIotaLinear linearEquations linearRules LinearSchema)

/-! ## The equations -/

/-- The equations of the executable package: those of `add` and `pow`, then the
program's equations of its constants, identity elimination with the repeated
point separated. -/
def equations : SchemaTable Tower.Head :=
  SetProfile.nativeEquations ++
    [jIotaLinear, numRecZeroEquation, numRecSucEquation, eqAtEquation, sucMoveEquation, keepEquation,
     transportEquation, composeEquation, iterZeroEquation, iterSucEquation, returnIterEquation,
     sucStepEquation]

theorem equation_listed (i : Nat) (h : i < equations.length) {arity : Nat}
    {left right : Tower.Tm arity} (same : equations[i] = ⟨arity, (left, right)⟩) :
    equations.family left right := by
  change (⟨arity, (left, right)⟩ : Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈ equations
  rw [← same]
  exact List.getElem_mem h

/-- The steps of the package are the steps of its listed computations. -/
theorem rules_computation {n : Nat} {l r : Tower.Tm n} :
    rules.computation.step l r ↔ ∃ entry ∈ computations, entry.2.step l r := by
  have filtered : computations.filter (fun entry => (fun _ => true) entry.1) = computations :=
    List.filter_eq_self.mpr fun _ _ => rfl
  constructor
  · intro step
    change (RootComputation.unionAll (computations.filter
      fun entry => (fun _ => true) entry.1)).step l r at step
    rw [filtered] at step
    exact RootComputation.unionAll_step step
  · rintro ⟨entry, mem, h⟩
    exact rules_step mem h

/-! ## Every instance of an equation is a step -/

theorem equation_sound {arity n : Nat} {left right : Tower.Tm arity}
    (rule : equations.family left right) (σ : Sub Tower.Head arity n) :
    rules.computation.step (subst σ left) (subst σ right) := by
  change (⟨arity, (left, right)⟩ : Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈ equations
    at rule
  simp only [equations, SetProfile.nativeEquations, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at rule
  rcases rule with (same | same | same | same) | (same | same | same | same | same | same |
    same | same | same | same | same | same) <;> cases same
  · refine rules_step (listed 1 (by decide)) ?_
    exact ⟨zeroN, [], consSub (.const zeroN) σ, [], mem_zero, rfl, rfl, rfl⟩
  · refine rules_step (listed 1 (by decide)) ?_
    exact ⟨sucN, [.recursive], consSub (.const zeroN) (fun _ => σ 1), [σ 0], mem_suc, rfl, rfl,
      rfl⟩
  · refine rules_step (listed 2 (by decide)) ?_
    exact ⟨zeroN, [], consSub (σ 0) (fun _ => .const zeroN), [], mem_zero, rfl, rfl, rfl⟩
  · refine rules_step (listed 2 (by decide)) ?_
    exact ⟨sucN, [.recursive], consSub (σ 0) (fun _ => .const zeroN), [σ 1], mem_suc, rfl, rfl,
      rfl⟩
  · refine rules_step (listed 3 (by decide)) ?_
    exact ⟨σ 5, σ 4, σ 3, σ 2, σ 1, σ 0, rfl, rfl⟩
  · refine rules_step (listed 0 (by decide)) ?_
    exact ⟨σ 2, [σ 1, σ 0], 0, zeroN, [], [], σ 1, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine rules_step (listed 0 (by decide)) ?_
    exact ⟨σ 3, [σ 2, σ 1], 1, sucN, [.recursive], [σ 0], σ 1, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine rules_step (listed 4 (by decide)) ?_
    exact ⟨σ, rfl, rfl⟩
  · refine rules_step (listed 5 (by decide)) ?_
    exact ⟨σ, rfl, rfl⟩
  · refine rules_step (listed 6 (by decide)) ?_
    exact ⟨σ, rfl, rfl⟩
  · refine rules_step (listed 7 (by decide)) ?_
    exact ⟨σ, rfl, rfl⟩
  · refine rules_step (listed 8 (by decide)) ?_
    exact ⟨σ, rfl, rfl⟩
  · refine rules_step (listed 9 (by decide)) ?_
    exact ⟨zeroN, [], consSub (σ 0) (consSub (σ 1) (consSub (σ 2) (consSub (σ 3)
      (consSub (σ 4) (fun _ => .const zeroN))))), [], mem_zero, rfl, rfl, rfl⟩
  · refine rules_step (listed 9 (by decide)) ?_
    exact ⟨sucN, [.recursive], σ, [σ 5], mem_suc, rfl, rfl, rfl⟩
  · refine rules_step (listed 10 (by decide)) ?_
    exact ⟨σ, rfl, rfl⟩
  · refine rules_step (listed 11 (by decide)) ?_
    exact ⟨σ, rfl, rfl⟩

/-! ## Every step is an instance of an equation -/

theorem equation_cover {n : Nat} {l r : Tower.Tm n} (step : rules.computation.step l r) :
    ∃ (arity : Nat) (left right : Tower.Tm arity) (σ : Sub Tower.Head arity n),
      equations.family left right ∧ subst σ left = l ∧ subst σ right = r := by
  obtain ⟨entry, mem, h⟩ := rules_computation.mp step
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
          exact ⟨3, _, _, consSub s (consSub z (consSub p Fin.elim0)),
            equation_listed 5 (by decide) rfl, rfl, rfl⟩
        · cases has
      · simp only [ctors, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        rcases args with _ | ⟨a, _ | ⟨_, _⟩⟩
        · cases has
        · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hm
          subst hm
          exact ⟨4, _, _, consSub a (consSub s (consSub z (consSub p Fin.elim0))),
            equation_listed 6 (by decide) rfl, rfl, rfl⟩
        · cases has
      · cases hi
    · cases hms
  · obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
    rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases as with _ | ⟨_, _⟩
      · exact ⟨1, _, _, consSub (σ 1) Fin.elim0, equation_listed 0 (by decide) rfl, rfl, rfl⟩
      · cases has
    · rcases as with _ | ⟨a, _ | ⟨_, _⟩⟩
      · cases has
      · exact ⟨2, _, _, consSub a (consSub (σ 1) Fin.elim0), equation_listed 1 (by decide) rfl,
          rfl, rfl⟩
      · cases has
  · obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
    rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases as with _ | ⟨_, _⟩
      · exact ⟨1, _, _, consSub (σ 0) Fin.elim0, equation_listed 2 (by decide) rfl, rfl, rfl⟩
      · cases has
    · rcases as with _ | ⟨a, _ | ⟨_, _⟩⟩
      · cases has
      · exact ⟨2, _, _, consSub (σ 0) (consSub a Fin.elim0), equation_listed 3 (by decide) rfl,
          rfl, rfl⟩
      · cases has
  · obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl, e⟩ := h
    exact ⟨6, _, _, consSub a₅ (consSub a₄ (consSub a₃ (consSub a₂ (consSub a₁
      (consSub a₀ Fin.elim0))))), equation_listed 4 (by decide) rfl, rfl, e.symm⟩
  · obtain ⟨σ, rfl, rfl⟩ := h
    exact ⟨1, _, _, σ, equation_listed 7 (by decide) rfl, rfl, rfl⟩
  · obtain ⟨σ, rfl, rfl⟩ := h
    exact ⟨2, _, _, σ, equation_listed 8 (by decide) rfl, rfl, rfl⟩
  · obtain ⟨σ, rfl, rfl⟩ := h
    exact ⟨4, _, _, σ, equation_listed 9 (by decide) rfl, rfl, rfl⟩
  · obtain ⟨σ, rfl, rfl⟩ := h
    exact ⟨6, _, _, σ, equation_listed 10 (by decide) rfl, rfl, rfl⟩
  · obtain ⟨σ, rfl, rfl⟩ := h
    exact ⟨6, _, _, σ, equation_listed 11 (by decide) rfl, rfl, rfl⟩
  · obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
    rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases as with _ | ⟨_, _⟩
      · exact ⟨5, _, _, consSub (σ 0) (consSub (σ 1) (consSub (σ 2) (consSub (σ 3)
          (consSub (σ 4) Fin.elim0)))), equation_listed 12 (by decide) rfl, rfl, rfl⟩
      · cases has
    · rcases as with _ | ⟨a, _ | ⟨_, _⟩⟩
      · cases has
      · have body : subst (hypSub iterName iterEntries 0 5 [.recursive])
            (iterBody sucN [.recursive]) = iterSucEquation.2.2 := rfl
        refine ⟨6, _, _, matchSub 0 1 [a] 5 σ, equation_listed 13 (by decide) rfl, rfl, ?_⟩
        rw [body]
        rfl
      · cases has
  · obtain ⟨σ, rfl, rfl⟩ := h
    exact ⟨1, _, _, σ, equation_listed 14 (by decide) rfl, rfl, rfl⟩
  · obtain ⟨σ, rfl, rfl⟩ := h
    exact ⟨2, _, _, σ, equation_listed 15 (by decide) rfl, rfl, rfl⟩

/-- The package's computation, presented by its equations. -/
def presentation : SchemaPresentation rules where
  schema := equations.family
  sound := equation_sound
  cover := equation_cover

/-! ## A constructor system -/

/-- The constants defined by the equations, with the number of their arguments. -/
def equationArities : List (DeclName × Nat) :=
  [(addN, 2), (powN, 2), (jName, 6), (numRecName, 4), (eqAtName, 1), (sucMoveName, 2),
   (keepName, 4), (transportName, 6), (composeName, 6), (iterName, 6), (returnIterName, 1),
   (sucStepName, 2)]

def EquationDefined (name : DeclName) : Prop := name ∈ equationArities.map Prod.fst

instance : DecidablePred EquationDefined :=
  fun name => inferInstanceAs (Decidable (name ∈ equationArities.map Prod.fst))

def equationArity (name : DeclName) : Nat := (equationArities.lookup name).getD 0

theorem equations_family {arity : Nat} {left right : Tower.Tm arity}
    (rule : equations.family left right) :
    (⟨arity, (left, right)⟩ : Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈ equations :=
  rule

theorem equation_left {m : Nat} {left right : Tower.Tm m} (rule : equations.family left right) :
    ∃ name, EquationDefined name ∧ 0 < equationArity name ∧
      LeftSide EquationDefined left name (equationArity name) := by
  have listed := equations_family rule
  simp only [equations, SetProfile.nativeEquations, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at listed
  rcases listed with (same | same | same | same) | (same | same | same | same | same | same |
    same | same | same | same | same | same) <;> cases same
  · exact ⟨addN, by decide, by decide, by show LeftSide EquationDefined _ addN 2; left_side⟩
  · exact ⟨addN, by decide, by decide, by show LeftSide EquationDefined _ addN 2; left_side⟩
  · exact ⟨powN, by decide, by decide, by show LeftSide EquationDefined _ powN 2; left_side⟩
  · exact ⟨powN, by decide, by decide, by show LeftSide EquationDefined _ powN 2; left_side⟩
  · exact ⟨jName, by decide, by decide, by show LeftSide EquationDefined _ jName 6; left_side⟩
  · exact ⟨numRecName, by decide, by decide,
      by show LeftSide EquationDefined _ numRecName 4; left_side⟩
  · exact ⟨numRecName, by decide, by decide,
      by show LeftSide EquationDefined _ numRecName 4; left_side⟩
  · exact ⟨eqAtName, by decide, by decide, by show LeftSide EquationDefined _ eqAtName 1; left_side⟩
  · exact ⟨sucMoveName, by decide, by decide,
      by show LeftSide EquationDefined _ sucMoveName 2; left_side⟩
  · exact ⟨keepName, by decide, by decide, by show LeftSide EquationDefined _ keepName 4; left_side⟩
  · exact ⟨transportName, by decide, by decide,
      by show LeftSide EquationDefined _ transportName 6; left_side⟩
  · exact ⟨composeName, by decide, by decide,
      by show LeftSide EquationDefined _ composeName 6; left_side⟩
  · exact ⟨iterName, by decide, by decide, by show LeftSide EquationDefined _ iterName 6; left_side⟩
  · exact ⟨iterName, by decide, by decide, by show LeftSide EquationDefined _ iterName 6; left_side⟩
  · exact ⟨returnIterName, by decide, by decide,
      by show LeftSide EquationDefined _ returnIterName 1; left_side⟩
  · exact ⟨sucStepName, by decide, by decide,
      by show LeftSide EquationDefined _ sucStepName 2; left_side⟩

theorem equation_linear : AlgebraicSchema.LeftLinearFamily equations.family := by
  intro m left right rule
  have listed := equations_family rule
  simp only [equations, SetProfile.nativeEquations, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at listed
  rcases listed with (same | same | same | same) | (same | same | same | same | same | same |
    same | same | same | same | same | same) <;> cases same <;> (unfold LeftLinear; decide)

theorem equation_covered {m : Nat} {left right : Tower.Tm m} (rule : equations.family left right) :
    ∀ index, 0 < variableMultiplicity index right → 0 < variableMultiplicity index left := by
  have listed := equations_family rule
  simp only [equations, SetProfile.nativeEquations, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at listed
  rcases listed with (same | same | same | same) | (same | same | same | same | same | same |
    same | same | same | same | same | same) <;> cases same <;> decide

theorem equations_disjoint : ∀ first ∈ equations, ∀ second ∈ equations,
    unifiable first.2.1 second.2.1 = true → first = second := by decide

theorem equation_disjoint {m m' : Nat} {left right : Tower.Tm m} {left' right' : Tower.Tm m'}
    (rule : equations.family left right) (rule' : equations.family left' right')
    (meet : unifiable left left' = true) :
    (⟨m, (left, right)⟩ : Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) =
      ⟨m', (left', right')⟩ :=
  equations_disjoint _ (equations_family rule) _ (equations_family rule') meet

/-- The equations as a definition by constructor patterns. -/
def system : System Tower.Head where
  schema := equations.family
  defined := EquationDefined
  arity := equationArity
  left := equation_left
  linear := equation_linear
  covered := equation_covered
  determined := Presentation.ConstructorSystem.determined_of_disjoint
    (fun rule => by
      obtain ⟨name, _, _, side⟩ := equation_left rule
      exact ⟨name, _, side⟩)
    equation_covered equation_disjoint

/-- The package, as a definition by constructor patterns. -/
def constructors : ConstructorPresentation rules where
  presentation := presentation
  system := system
  same := fun _ _ => Iff.rfl
  symmetric := LevelTower.headEq_symmetric

/-! ## Church–Rosser and conservativity -/

/-- The package's conversion is Church–Rosser. -/
theorem churchRosser : ChurchRosser rules := constructors.churchRosser

theorem piConversionBoundary : PiConversionBoundary rules :=
  constructors.piConversionBoundary

theorem sigmaConversionBoundary : SigmaConversionBoundary rules :=
  constructors.sigmaConversionBoundary

/-- Convertible typed terms of the package are equal in the typed equality. -/
theorem conv_toEqual {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed rules Γ)
    {a b T : Tower.Tm n} (conversion : Conv rules.headEq a b rules.computation)
    (ta : Typed rules Γ a T) (tb : Typed rules Γ b T) : Equal rules Γ a b T :=
  Presentation.TypedEquality.Normalization.Conv.toEqual (S := setting fun _ => 0) facts roots
      heads churchRosser formed conversion ta tb

/-- Every formation-sensitive typing derivation of the package in a formed
context is a typing derivation of the typed equality. -/
theorem formationSensitive_toTyped {n : Nat} {Γ : Tower.Ctx n} {t A : Tower.Tm n}
    (typing : FormationSensitive.Typing rules Γ t A) (formed : CtxFormed rules Γ) :
    Typed rules Γ t A :=
  Presentation.TypedEquality.Normalization.FormationSensitive.Typing.toTyped
    (S := setting fun _ => 0) facts roots heads churchRosser typing formed

/-! ## Inside the linearized program -/

/-- The equations are equations of the linearized program. -/
theorem equation_linearSchema {arity : Nat} {left right : Tower.Tm arity}
    (rule : equations.family left right) : LinearSchema left right := by
  rcases List.mem_append.mp (equations_family rule) with native | package
  · exact .native native
  · refine .package ?_
    have split : linearEquations =
        [jIotaLinear, numRecZeroEquation, numRecSucEquation, eqAtEquation, sucMoveEquation, keepEquation,
          transportEquation, composeEquation, iterZeroEquation, iterSucEquation, returnIterEquation,
          sucStepEquation] ++
        [Package.holdsAtEquation, Package.holdsMoveEquation, Package.holdsStepEquation] := rfl
    rw [split]
    exact List.mem_append_left _ package

theorem profile_linear {name : DeclName} {type : Tower.Tm 0}
    (known : SetProfile.rules.constantType name = some type) :
    linearRules.constantType name = some type := by
  simpa only [Tm.mapHead_id] using
    Confluence.packageToLinear.constantType (Package.profileMorphism.constantType known)

theorem package_linear {name : DeclName} {type : Tower.Tm 0}
    (known : Package.packageRules.constantType name = some type) :
    linearRules.constantType name = some type := by
  simpa only [Tm.mapHead_id] using Confluence.packageToLinear.constantType known

/-- The package's declared types are the linearized program's. -/
theorem linear_constantType {name : DeclName} {type : Tower.Tm 0}
    (declared : rules.constantType name = some type) :
    linearRules.constantType name = some type := by
  change (if true then allTypes name else none) = some type at declared
  rw [if_pos rfl] at declared
  have mem := mem_of_lookup (show declarations.lookup name = some type from declared)
  simp only [declarations, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
  rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact profile_linear (SetProfile.lookup_base .num)
  · exact profile_linear (SetProfile.lookup_base .set)
  · exact profile_linear (SetProfile.lookup_constant .zero)
  · exact profile_linear (SetProfile.lookup_constant .suc)
  · exact profile_linear (SetProfile.lookup_constant .add)
  · exact profile_linear (SetProfile.lookup_constant .power)
  · exact profile_linear (SetProfile.lookup_constant .pow)
  · exact package_linear Package.lookup_numRec
  · exact package_linear Package.lookup_j
  · exact package_linear Package.lookup_eqAt
  · exact package_linear Package.lookup_sucMove
  · exact package_linear Package.lookup_keep
  · exact package_linear Package.lookup_transport
  · exact package_linear Package.lookup_compose
  · exact package_linear Package.lookup_iter
  · exact package_linear Package.lookup_returnIter
  · exact package_linear Package.lookup_sucStep

/-- Every step of the package is a step of the linearized program. -/
theorem linear_step {n : Nat} {l r : Tower.Tm n} (step : rules.computation.step l r) :
    linearRules.computation.step l r := by
  obtain ⟨arity, left, right, σ, rule, rfl, rfl⟩ := equation_cover step
  exact Confluence.linearSchema_sound (equation_linearSchema rule) σ

/-- The package is a sub-package of the linearized program. -/
theorem sub_linear : RulesSub rules linearRules where
  headTyping := fun typing => typing
  isUniverse := fun isU => isU
  join := fun joined => joined
  cumulative := fun order => order
  headEq := fun equality => equality
  constantType := linear_constantType
  computation := linear_step

theorem toLinear : rules.Morphism linearRules (fun head => head) where
  headTyping := fun typing => typing
  isUniverse := fun isU => isU
  join := fun joined => joined
  cumulative := fun order => order
  headEq := fun equality => equality
  constantType := by
    intro name type known
    simpa only [Tm.mapHead_id] using linear_constantType known
  computation := by
    intro n l r step
    simpa only [Tm.mapHead_id] using linear_step step

/-- The package's typings are typings of the linearized program. -/
theorem typing_linear {n : Nat} {Γ : Tower.Ctx n} {t A : Tower.Tm n}
    (typing : FormationSensitive.Typing rules Γ t A) :
    FormationSensitive.Typing linearRules Γ t A := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using typing.mapHead toLinear

/-- The package's typed equalities are typed equalities of the linearized
program. -/
theorem equal_linear {n : Nat} {Γ : Tower.Ctx n} {a b A : Tower.Tm n}
    (equal : Equal rules Γ a b A) : Equal linearRules Γ a b A :=
  Derivable.mono sub_linear equal

theorem typed_linear {n : Nat} {Γ : Tower.Ctx n} {t A : Tower.Tm n}
    (typed : Typed rules Γ t A) : Typed linearRules Γ t A :=
  Derivable.mono sub_linear typed

/-! ## Axiom audit -/

#print axioms j_endpoints
#print axioms j_mismatch_untyped
#print axioms equation_sound
#print axioms equation_cover
#print axioms churchRosser
#print axioms conv_toEqual
#print axioms formationSensitive_toTyped
#print axioms sub_linear
#print axioms typing_linear
#print axioms typed_linear

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
