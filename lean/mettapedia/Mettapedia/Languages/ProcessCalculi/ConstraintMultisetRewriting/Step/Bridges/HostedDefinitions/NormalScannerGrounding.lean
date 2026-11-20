import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalProbeFreshness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalProbeExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalStructure

/-!
# Native fields in actual copied scanner clauses

The native constructor view only exposes its encoded fields. A live scanner
match determines every used copied field in arbitrary target families. The
proof uses rigid literal paths, rather than equality of closed readings.
Copied scanner bodies retain their real binder sites and site-0 field names.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerGrounding

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open NativeTypesOnTheStep.Computing

local instance closedTerms : ProgramBinders.ClosedTerms MSig where
  closed := fun | () => csym "closed-hole"

def kind : {n : Nat} → Tower.Tm n → NormalScanner.Constructor
  | _, .var _ => .var
  | _, .const _ => .const
  | _, .head _ => .head
  | _, .pi _ _ => .pi
  | _, .sigma _ _ => .sigma
  | _, .id _ _ _ => .id
  | _, .lam _ => .lam
  | _, .app _ _ => .app
  | _, .pair _ _ => .pair
  | _, .fst _ => .fst
  | _, .snd _ => .snd
  | _, .refl _ => .refl

def values : {n : Nat} → Tower.Tm n → Fin 3 → MClosed
  | _, .var index, _ => encodeNat index.val
  | _, .const name, _ => encodeName name
  | _, .head head, _ => encodeHead head
  | _, .pi first second, index | _, .sigma first second, index =>
      if index = 0 then encodeTm first else encodeTm second
  | _, .id carrier left right, index =>
      if index = 0 then encodeTm carrier else if index = 1 then encodeTm left else encodeTm right
  | _, .lam body, _ => encodeTm body
  | _, .app first second, index | _, .pair first second, index =>
      if index = 0 then encodeTm first else encodeTm second
  | _, .fst subject, _ | _, .snd subject, _ | _, .refl subject, _ => encodeTm subject

theorem encode_instance {n : Nat} (term : Tower.Tm n) :
    encodeTm term = nodeC (kind term).tag ((kind term).fields.map (values term)) := by
  cases term <;> simp [kind, values, NormalScanner.Constructor.tag, NormalScanner.Constructor.fields]

variable {dev : Definitions.Development} (built : Compiled dev)

def childJobs : NormalScanner.Constructor → List (Fin 5 × Fin 3)
  | .var | .const | .head => []
  | .pi | .sigma | .app | .pair => [(2, 0), (3, 1)]
  | .id => [(2, 0), (3, 1), (4, 2)]
  | _ => [(2, 0)]

def checkChain {Ty : Type} (jobs : List (Fin 5 × Fin 3)) :
    Comp (BinderCore.keys built.rules) [] () Ty :=
  jobs.foldr (fun job body => NormalScanner.childTest built job.1 job.2 body)
    (.ret (NormalScanner.marker (fam (BinderCore.keys built.rules))))

theorem childTests_eq_chain {Ty : Type} (ctor : NormalScanner.Constructor) :
    NormalScanner.childTests built (Ty := Ty) ctor = checkChain built (childJobs ctor) := by
  cases ctor <;> rfl

theorem childJobs_sites (ctor : NormalScanner.Constructor) (job : Fin 5 × Fin 3)
    (inside : job ∈ childJobs ctor) : job.1 ≠ 0 ∧ job.2 ∈ ctor.fields := by
  cases ctor <;>
    simp only [childJobs, NormalScanner.Constructor.fields, List.mem_cons,
      List.not_mem_nil, or_false] at inside ⊢
  all_goals first
    | contradiction
    | rcases inside with rfl | rfl | rfl <;> decide +kernel

def field_assignment {X : Type} (target : X → MetaArity MSig) (environment : Fin 3 → MClosed) :
    Assignment (fam (BinderCore.keys built.rules)) target :=
  NormalProbeFreshness.equationAssignment built target (NormalScanner.site built 0) environment

theorem read_datum {X : Type} (target : X → MetaArity MSig)
    (environment : Fin 3 → MClosed) (index : Fin 3) :
    instantiate (field_assignment built target environment) (NormalScanner.datum built index) =
      Rigid.includeTerm target (environment index) := by
  change instantiate (field_assignment built target environment)
    (generator (fam (BinderCore.keys built.rules)) ⟨[], NormalScanner.key built index⟩) = _
  rw [instantiate_generator]
  change Rigid.includeTerm target (ProgramBinders.extendGround built.rules.get
    (NormalScanner.site built 0) environment ⟨NormalScanner.site built 0, NormalScanner.hole built index⟩) = _
  rw [congrFun (ProgramBinders.extendGround_at built.rules.get
    (NormalScanner.site built 0) environment) (NormalScanner.hole built index)]
  rfl

theorem read_pattern {X : Type} (target : X → MetaArity MSig)
    (environment : Fin 3 → MClosed) (ctor : NormalScanner.Constructor) :
    instantiate (field_assignment built target environment) (NormalScanner.pattern built ctor) =
      Rigid.includeTerm target (nodeC ctor.tag (ctor.fields.map environment)) := by
  rw [NormalScanner.instantiate_pattern, NormalScanner.include_nodeAt]
  simp only [List.map_map, Function.comp_def, read_datum]

theorem field_path (ctor : NormalScanner.Constructor) (index : Fin 3)
    (used : index ∈ ctor.fields) :
    LiteralPaths.part (NormalScanner.pattern built ctor) [index.val + 1] =
      some (NormalScanner.datum built index) := by
  cases ctor <;> fin_cases index <;> first
    | rfl
    | simp [NormalScanner.Constructor.fields] at used

def matchStore (scope : Nat) (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ()) (ctor : NormalScanner.Constructor) :
    List (Constraint (BinderCore.keys built.rules) [] ()) :=
  K ++ [(instantiate (copyAt (BinderCore.keys built.rules) scope)
    (NormalScanner.scanAt (NormalScanner.pattern built ctor)), NormalScanner.scanAt datum)]

theorem copied_pattern_determines (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ()) (ctor : NormalScanner.Constructor)
    (code : MClosed) (determined : Determines K datum code)
    (live : Solvable (matchStore built scope K datum ctor)) :
    Determines (matchStore built scope K datum ctor)
      (instantiate (copyAt (BinderCore.keys built.rules) scope) (NormalScanner.pattern built ctor)) code := by
  refine ⟨live, ?_⟩
  intro X target assignment solved
  obtain ⟨old, added⟩ := (models_append assignment _ _).mp solved
  have same := (models_singleton assignment _).mp added
  rw [NormalScanner.instantiate_scanAt, NormalScanner.instantiate_scanAt,
    NormalScanner.instantiate_scanAt] at same
  exact ((NormalScanner.scanAt_eq_iff _ _).mp same).trans (determined.2 target assignment old)

theorem copied_field_determines (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ()) (ctor : NormalScanner.Constructor)
    (environment : Fin 3 → MClosed) (code : MClosed)
    (encoded : code = nodeC ctor.tag (ctor.fields.map environment))
    (determined : Determines K datum code)
    (live : Solvable (matchStore built scope K datum ctor))
    (index : Fin 3) (used : index ∈ ctor.fields) :
    Determines (matchStore built scope K datum ctor)
      (instantiate (copyAt (BinderCore.keys built.rules) scope) (NormalScanner.datum built index))
      (environment index) := by
  have pattern := copied_pattern_determines built scope K datum ctor code determined live
  refine ⟨live, ?_⟩
  intro X target assignment solved
  have same := pattern.2 target assignment solved
  rw [encoded] at same
  have aligned := same.trans (read_pattern built target environment ctor).symm
  have path := field_path built ctor index used
  have leftPath := LiteralPaths.part_instantiate assignment
    (LiteralPaths.part_instantiate (copyAt (BinderCore.keys built.rules) scope) path)
  have rightPath := LiteralPaths.part_instantiate (field_assignment built target environment) path
  have parts := congrArg (fun term => LiteralPaths.part term [index.val + 1]) aligned
  rw [leftPath, rightPath] at parts
  exact (Option.some.inj parts).trans (read_datum built target environment index)

theorem match_live (scope : Nat) (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ()) (ctor : NormalScanner.Constructor)
    (environment : Fin 3 → MClosed) (code : MClosed)
    (encoded : code = nodeC ctor.tag (ctor.fields.map environment))
    (storeBelow : Hosting.StoreBelow scope K)
    (callBelow : Hosting.DependsBelow scope (NormalScanner.scanAt datum))
    (determined : Determines K datum code) : Solvable (matchStore built scope K datum ctor) := by
  obtain ⟨X, target, assignment, solved⟩ := determined.1
  apply (Hosting.solvable_copy_iff (NormalScanner.scanAt (NormalScanner.pattern built ctor))
    storeBelow callBelow).mpr
  refine ⟨X, target, assignment, field_assignment built target environment, solved, ?_⟩
  rw [NormalScanner.instantiate_scanAt, NormalScanner.instantiate_scanAt,
    read_pattern, determined.2 target assignment solved, encoded]

theorem determines_append {K extra : List (Constraint (BinderCore.keys built.rules) [] ())}
    {datum : Data (BinderCore.keys built.rules) [] ()} {code : MClosed}
    (determined : Determines K datum code) (live : Solvable (K ++ extra)) :
    Determines (K ++ extra) datum code :=
  ⟨live, fun target assignment solved =>
    determined.2 target assignment ((models_append assignment _ _).mp solved).1⟩

theorem determines_root {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    {datum : Data (BinderCore.keys built.rules) [] ()} {code : MClosed}
    (determined : Determines K datum code) :
    Determines K (NormalScanner.rootAt datum) (rootC code (csym NormalScanner.stopTag)) := by
  refine ⟨determined.1, ?_⟩
  intro X target assignment solved
  rw [NormalScanner.instantiate_rootAt, determined.2 target assignment solved,
    NormalScanner.include_rootAt]

theorem instantiate_rootTest {Ty : Type}
    (assignment : Assignment (fam (BinderCore.keys built.rules)) (fam (BinderCore.keys built.rules)))
    (datum : Data (BinderCore.keys built.rules) [] ())
    (continuation : Comp (BinderCore.keys built.rules) [] () Ty) :
    (NormalScanner.rootTest built datum continuation).inst assignment =
      NormalScanner.rootTest built (instantiate assignment datum) (continuation.inst assignment) := by
  simp only [NormalScanner.rootTest, Comp.inst, Comp.mapData, NormalScanner.instantiate_probeAt]

theorem copied_equation_rhs (D : Discipline MSig [] ()) (ctor : NormalScanner.Constructor)
    (scope : Nat) :
    (NormalScanner.equation built D ctor).rhs.inst (copyAt (BinderCore.keys built.rules) scope) =
      NormalScanner.rootTest built
        (instantiate (copyAt (BinderCore.keys built.rules) scope) (NormalScanner.pattern built ctor))
        ((NormalScanner.childTests built ctor).inst (copyAt (BinderCore.keys built.rules) scope)) :=
  instantiate_rootTest built _ _ _

theorem callBranch_shape (D : Discipline MSig [] ()) (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ()) (ctor : NormalScanner.Constructor)
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty)) :
    callBranch D scope K (NormalScanner.scanAt datum) frames pending (NormalScanner.equation built D ctor) =
      ⟨matchStore built scope K datum ctor,
        .eval (NormalScanner.rootTest built
          (instantiate (copyAt (BinderCore.keys built.rules) scope) (NormalScanner.pattern built ctor))
          ((NormalScanner.childTests built ctor).inst (copyAt (BinderCore.keys built.rules) scope))),
        frames, pending⟩ := by
  change (⟨matchStore built scope K datum ctor,
    .eval ((NormalScanner.equation built D ctor).rhs.inst (copyAt (BinderCore.keys built.rules) scope)),
    frames, pending⟩ : Branch (BinderCore.keys built.rules) [] () D.Ty) = _
  rw [copied_equation_rhs]

theorem open_copied_datum (copyScope scope : Nat) (bindSite : Fin 5) (different : bindSite ≠ 0)
    (index : Fin 3) :
    instantiate (openAt (BinderCore.keys built.rules) (NormalScanner.site built bindSite) scope)
      (instantiate (copyAt (BinderCore.keys built.rules) copyScope) (NormalScanner.datum built index)) =
        instantiate (copyAt (BinderCore.keys built.rules) copyScope) (NormalScanner.datum built index) := by
  rw [instantiate_comp]
  apply instantiate_congr
  intro name used
  change name ∈ support (generator (fam (BinderCore.keys built.rules))
    ⟨[], NormalScanner.key built index⟩) at used
  have same : name = ⟨[], NormalScanner.key built index⟩ := by
    simpa only [support_generator, List.mem_singleton] using used
  subst name
  change instantiate (openAt (BinderCore.keys built.rules) (NormalScanner.site built bindSite) scope)
    (nameAt (BinderCore.keys built.rules) [copyScope] (NormalScanner.key built index)) =
      nameAt (BinderCore.keys built.rules) [copyScope] (NormalScanner.key built index)
  exact NormalScanner.open_datum built bindSite different scope [copyScope] index

theorem open_copied_pattern (ctor : NormalScanner.Constructor) (copyScope scope : Nat)
    (bindSite : Fin 5) (different : bindSite ≠ 0) :
    instantiate (openAt (BinderCore.keys built.rules) (NormalScanner.site built bindSite) scope)
      (instantiate (copyAt (BinderCore.keys built.rules) copyScope) (NormalScanner.pattern built ctor)) =
        instantiate (copyAt (BinderCore.keys built.rules) copyScope) (NormalScanner.pattern built ctor) := by
  simp only [NormalScanner.instantiate_pattern, NormalScanner.instantiate_nodeAt]
  rw [List.map_map]
  apply congrArg (NormalScanner.nodeAt ctor.tag)
  apply List.map_congr_left
  intro index _
  exact open_copied_datum built copyScope scope bindSite different index

theorem open_copied_childTests {Ty : Type} (ctor : NormalScanner.Constructor)
    (copyScope scope : Nat) (bindSite : Fin 5) (different : bindSite ≠ 0) :
    ((NormalScanner.childTests built (Ty := Ty) ctor).inst
      (copyAt (BinderCore.keys built.rules) copyScope)).inst
        (openAt (BinderCore.keys built.rules) (NormalScanner.site built bindSite) scope) =
      (NormalScanner.childTests built ctor).inst (copyAt (BinderCore.keys built.rules) copyScope) := by
  cases ctor <;>
    simp only [NormalScanner.childTests, NormalScanner.childTest, Comp.inst, Comp.mapData,
      NormalScanner.instantiate_marker, NormalScanner.instantiate_scanAt]
  all_goals simp only [open_copied_datum built copyScope scope bindSite different]

theorem open_copied_chain {Ty : Type} (jobs : List (Fin 5 × Fin 3))
    (copyScope scope : Nat) (bindSite : Fin 5) (different : bindSite ≠ 0) :
    ((checkChain built (Ty := Ty) jobs).inst (copyAt (BinderCore.keys built.rules) copyScope)).inst
      (openAt (BinderCore.keys built.rules) (NormalScanner.site built bindSite) scope) =
      (checkChain built jobs).inst (copyAt (BinderCore.keys built.rules) copyScope) := by
  induction jobs with
  | nil => rfl
  | cons job jobs ih =>
      change ((NormalScanner.childTest built job.1 job.2 (checkChain built jobs)).inst
        (copyAt (BinderCore.keys built.rules) copyScope)).inst
          (openAt (BinderCore.keys built.rules) (NormalScanner.site built bindSite) scope) =
        (NormalScanner.childTest built job.1 job.2 (checkChain built jobs)).inst
          (copyAt (BinderCore.keys built.rules) copyScope)
      simp only [NormalScanner.childTest, Comp.inst, Comp.mapData,
        NormalScanner.instantiate_marker, NormalScanner.instantiate_scanAt]
      rw [open_copied_datum built copyScope scope bindSite different]
      exact congrArg (fun body => Comp.let_ (NormalScanner.site built job.1)
        (NormalScanner.marker (fam (BinderCore.keys built.rules)))
        (.apply (NormalScanner.scanAt
          (instantiate (copyAt (BinderCore.keys built.rules) copyScope) (NormalScanner.datum built job.2)))) body) ih

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerGrounding

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerGrounding.copied_field_determines
