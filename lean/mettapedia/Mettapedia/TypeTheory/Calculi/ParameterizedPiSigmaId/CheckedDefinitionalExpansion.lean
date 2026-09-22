import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DefinitionalExpansion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSignaturePreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TelescopeAbstraction
import Mettapedia.Logic.Function.RankedIteration

/-!
# Computed qualification of finite transparent declaration packages

Finite expansion rounds compute closed replacement bodies from the existing
first-match signature lookup. A finite syntactic compatibility check then
qualifies these computed bodies for the existing full conversion theorem.
No user-supplied conversion proof or contextual preservation theorem is an
input to this check.

Insufficient rounds may fail the check. Failure does not refute conversion,
and success is not a termination certificate: an operational self-loop can
preserve conversion classes. Formation and typing of definition bodies remain
independent obligations for logical subject preservation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ConstantExpansion.Checked

open Declaration

variable {Head : Type}

/-- One simultaneous unfolding step, with opaque and missing names retained. -/
def advance (signature : Signature Head) (previous : Bodies Head) : Bodies Head :=
  fun name =>
    match signature.valueOf? name with
    | none => .const name
    | some body => expand previous body

/-- One round unfolds each selected transparent constant, using the previous
round for constants in its body. Opaque and missing names remain unchanged. -/
def bodies (signature : Signature Head) : Nat → Bodies Head
  | 0 => fun name => .const name
  | rounds + 1 => advance signature (bodies signature rounds)

theorem bodies_eq_iterate (signature : Signature Head) (rounds : Nat) :
    bodies signature rounds = (advance signature)^[rounds] (fun name => .const name) := by
  induction rounds with
  | zero => rfl
  | succ rounds ih => rw [bodies, ih, Function.iterate_succ_apply']

@[simp] theorem bodies_of_opaque (signature : Signature Head) (rounds : Nat)
    {name : DeclName} (opaqueName : signature.valueOf? name = none) :
    bodies signature rounds name = .const name := by
  cases rounds <;> simp [bodies, advance, opaqueName]

/-- Every finite round is justified by actual source delta steps, regardless
of whether the final compatibility check succeeds. -/
theorem constants_convert (base : Rules Head) (signature : Signature Head)
    (rounds : Nat) (name : DeclName) :
    Conv base.headEq (.const name) (bodies signature rounds name)
      (rootComputation base signature) := by
  induction rounds generalizing name with
  | zero => exact .refl _
  | succ rounds ih =>
      simp only [bodies, advance]
      cases known : signature.valueOf? name with
      | none => exact .refl _
      | some body =>
          have first : Conv base.headEq (.const name : Tm Head 0) body
              (rootComputation base signature) := by
            simpa only [TelescopeAbstraction.liftClosed_zero] using
              (Relation.EqvGen.rel _ _
                (Step.root (root := rootComputation base signature)
                  (RootStep.delta (base := base) (n := 0) known)))
          exact .trans _ _ _ first (term_conv_expand _ ih body)

/-- Equality here is finite syntax equality after the computed expansion,
not a call to the conversion relation being qualified. -/
def check [DecidableEq Head] (entries : List (DeclName × Entry Head)) (rounds : Nat) : Bool :=
  entries.all fun entry =>
    match (Signature.ofList entries).valueOf? entry.1 with
    | none => true
    | some body => decide (bodies (Signature.ofList entries) rounds entry.1 =
        expand (bodies (Signature.ofList entries) rounds) body)

theorem check_definitions [DecidableEq Head]
    (entries : List (DeclName × Entry Head)) (rounds : Nat)
    (accepted : check entries rounds = true)
    {name : DeclName} {value : Tm Head 0}
    (known : (Signature.ofList entries).valueOf? name = some value) :
    bodies (Signature.ofList entries) rounds name =
      expand (bodies (Signature.ofList entries) rounds) value := by
  obtain ⟨entry, member, same⟩ := List.mem_map.mp (Signature.valueOf_name_mem entries known)
  subst name
  have compared := List.all_eq_true.mp accepted entry member
  simpa only [known, decide_eq_true_eq] using compared

/-- The finite check is exactly a fixed-point test on the generated bodies.
The equivalence quantifies over every name, including absent and opaque names. -/
theorem check_iff_fixed_point [DecidableEq Head]
    (entries : List (DeclName × Entry Head)) (rounds : Nat) :
    check entries rounds = true ↔
      bodies (Signature.ofList entries) (rounds + 1) =
        bodies (Signature.ofList entries) rounds := by
  constructor
  · intro accepted
    funext name
    cases known : (Signature.ofList entries).valueOf? name with
    | none => simp [bodies, advance, known]
    | some value =>
        simpa only [bodies, advance, known] using
          (check_definitions entries rounds accepted known).symm
  · intro fixed
    apply List.all_eq_true.mpr
    intro entry _member
    cases known : (Signature.ofList entries).valueOf? entry.1 with
    | none => rfl
    | some value =>
        have atName := congrFun fixed entry.1
        simp only [bodies, advance, known] at atName
        simpa only [known, decide_eq_true_eq] using atName.symm

/-- Once accepted, increasing the expansion budget cannot change its result. -/
theorem bodies_stable [DecidableEq Head]
    (entries : List (DeclName × Entry Head)) (rounds : Nat)
    (accepted : check entries rounds = true) (extra : Nat) :
    bodies (Signature.ofList entries) (rounds + extra) =
      bodies (Signature.ofList entries) rounds := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      have fixed := (check_iff_fixed_point entries rounds).mp accepted
      have next : bodies (Signature.ofList entries) (rounds + (extra + 1)) =
          bodies (Signature.ofList entries) (rounds + 1) := by
        funext name
        change (match (Signature.ofList entries).valueOf? name with
          | none => (Tm.const name : Tm Head 0)
          | some value => expand (bodies (Signature.ofList entries) (rounds + extra)) value) =
          (match (Signature.ofList entries).valueOf? name with
          | none => (Tm.const name : Tm Head 0)
          | some value => expand (bodies (Signature.ofList entries) rounds) value)
        rw [ih]
      exact next.trans fixed

theorem check_stable [DecidableEq Head]
    (entries : List (DeclName × Entry Head)) (rounds : Nat)
    (accepted : check entries rounds = true) (extra : Nat) :
    check entries (rounds + extra) = true := by
  apply (check_iff_fixed_point entries (rounds + extra)).mpr
  rw [show rounds + extra + 1 = rounds + (extra + 1) by omega,
    bodies_stable entries rounds accepted (extra + 1),
    bodies_stable entries rounds accepted extra]

/-- Successful finite checking supplies all primitive conversion obligations
of the previously established qualification. The computed bodies are retained. -/
def qualification [DecidableEq Head] (base : Rules Head)
    (baseEmpty : base.computation = RootComputation.empty)
    (entries : List (DeclName × Entry Head)) (rounds : Nat)
    (accepted : check entries rounds = true) :
    Qualification (extendRules base (Signature.ofList entries)) :=
  Qualification.ofSignature base (Signature.ofList entries) baseEmpty
    (bodies (Signature.ofList entries) rounds) (constants_convert base _ rounds)
    (fun _ _ known => by
      rw [check_definitions entries rounds accepted known]
      exact .refl _)
    (by
      intro n left right impossible
      rw [Signature.computation_ofList] at impossible
      exact impossible.elim)

/-- A partial compiler for the finite expansion qualifier. Its only proof
input fixes the inherited computation policy; acceptance is earned by `check`. -/
def qualify? [DecidableEq Head] (base : Rules Head)
    (baseEmpty : base.computation = RootComputation.empty)
    (entries : List (DeclName × Entry Head)) (rounds : Nat) :
    Option (Qualification (extendRules base (Signature.ofList entries))) :=
  if accepted : check entries rounds = true then
    some (qualification base baseEmpty entries rounds accepted)
  else none

@[simp] theorem qualify_isSome [DecidableEq Head] (base : Rules Head)
    (baseEmpty : base.computation = RootComputation.empty)
    (entries : List (DeclName × Entry Head)) (rounds : Nat) :
    (qualify? base baseEmpty entries rounds).isSome = check entries rounds := by
  unfold qualify?
  split <;> simp_all

/-- The returned certificate contains the actual generated bodies, not an
existentially selected alternative expansion. -/
theorem qualify_bodies [DecidableEq Head] (base : Rules Head)
    (baseEmpty : base.computation = RootComputation.empty)
    (entries : List (DeclName × Entry Head)) (rounds : Nat)
    {result : Qualification (extendRules base (Signature.ofList entries))}
    (computed : qualify? base baseEmpty entries rounds = some result) :
    result.bodies = bodies (Signature.ofList entries) rounds := by
  unfold qualify? at computed
  split at computed
  · cases computed
    rfl
  · contradiction

/-- Successful checking earns full contextual conversion preservation and
reflection for arbitrary open terms, through the original qualification law. -/
theorem conversion_iff [DecidableEq Head] (base : Rules Head)
    (baseEmpty : base.computation = RootComputation.empty)
    (entries : List (DeclName × Entry Head)) (rounds : Nat)
    (accepted : check entries rounds = true)
    {n : Nat} (left right : Tm Head n) :
    Conv base.headEq left right (rootComputation base (Signature.ofList entries)) ↔
      Conv base.headEq (expand (bodies (Signature.ofList entries) rounds) left)
        (expand (bodies (Signature.ofList entries) rounds) right) :=
  (qualification base baseEmpty entries rounds accepted).conversion_iff left right

/-- For independently typed definitions, the computed qualifier discharges
the conversion boundary in the general contextual subject-reduction theorem. -/
theorem steps_preserve [DecidableEq Head] (base : Rules Head)
    (baseEmpty : base.computation = RootComputation.empty)
    (entries : List (DeclName × Entry Head)) (rounds : Nat)
    (accepted : check entries rounds = true)
    (universes : FormationSensitive.UniverseRegularity base)
    (heads : FormationSensitive.HeadPreservation base)
    (symmetric : Std.Symm base.headEq)
    (typed : ∀ name body, (Signature.ofList entries).valueOf? name = some body →
      ∃ declared, (extendRules base (Signature.ofList entries)).constantType name = some declared ∧
        FormationSensitive.Typing (extendRules base (Signature.ofList entries)) .nil body declared)
    {n : Nat} {context : Ctx Head n} {source target type : Tm Head n}
    (judgment : FormationSensitive.Judgment (extendRules base (Signature.ofList entries)) context source type)
    (steps : ConversionCoherence.StepStar (extendRules base (Signature.ofList entries)) source target) :
    FormationSensitive.Judgment (extendRules base (Signature.ofList entries)) context target type :=
  judgment.steps_preserve_definitions baseEmpty (Signature.computation_ofList entries) universes heads symmetric
    (qualification base baseEmpty entries rounds accepted) typed steps

namespace Ordered

/-- The first selected transparent declaration gets its position plus one.
Opaque and absent names have rank zero, since unfolding never changes them. -/
def rank (entries : List (DeclName × Entry Head)) (name : DeclName) : Nat :=
  if ((Signature.ofList entries).valueOf? name).isSome then
    (entries.map Prod.fst).idxOf name + 1
  else 0

theorem rank_lt_bound (entries : List (DeclName × Entry Head)) (name : DeclName) :
    rank entries name < entries.length + 1 := by
  cases known : (Signature.ofList entries).valueOf? name with
  | none => simp [rank, known]
  | some body =>
      have member := Signature.valueOf_name_mem entries known
      have bounded := List.idxOf_lt_length_iff.mpr member
      simp only [List.length_map] at bounded
      simpa only [rank, known, Option.isSome_some, ite_true] using Nat.succ_lt_succ bounded

/-- Check dependencies in selected bodies, using the same first-match lookup
as execution. This sufficient order test does not inspect unselected bodies,
and it is not a type checker or a decision procedure for all acyclic orders. -/
def check (entries : List (DeclName × Entry Head)) : Bool :=
  entries.all fun entry =>
    match (Signature.ofList entries).valueOf? entry.1 with
    | none => true
    | some body => (constantNames body).all fun dependency =>
        decide (rank entries dependency < rank entries entry.1)

/-- The finite inventory test covers every selected definition and every
constant occurring in its body, including below dependent binders. -/
theorem check_iff_decreases (entries : List (DeclName × Entry Head)) :
    check entries = true ↔
      ∀ name body, (Signature.ofList entries).valueOf? name = some body →
        ∀ dependency ∈ constantNames body, rank entries dependency < rank entries name := by
  constructor
  · intro accepted name body known dependency occurs
    obtain ⟨entry, member, same⟩ := List.mem_map.mp (Signature.valueOf_name_mem entries known)
    subst name
    have checked := List.all_eq_true.mp accepted entry member
    simp only [known] at checked
    exact of_decide_eq_true (List.all_eq_true.mp checked dependency occurs)
  · intro decreases
    apply List.all_eq_true.mpr
    intro entry _member
    cases known : (Signature.ofList entries).valueOf? entry.1 with
    | none => rfl
    | some body =>
        apply List.all_eq_true.mpr
        intro dependency occurs
        exact decide_eq_true (decreases entry.1 body known dependency occurs)

/-- Ordered transparent definitions reach a fixed point within the computed
inventory bound. This uses the general dependency-local iteration theorem;
no fixed-point or conversion assumption is supplied by the caller. -/
theorem bodies_fixed (entries : List (DeclName × Entry Head))
    (ordered : check entries = true) :
    bodies (Signature.ofList entries) (entries.length + 1 + 1) =
      bodies (Signature.ofList entries) (entries.length + 1) := by
  rw [bodies_eq_iterate, bodies_eq_iterate]
  apply Mettapedia.Logic.Function.iterate_fixed_of_rank_bound
    (advance (Signature.ofList entries))
    (fun name dependency => ∃ body,
      (Signature.ofList entries).valueOf? name = some body ∧ dependency ∈ constantNames body)
    (rank entries)
  · intro name first second agree
    cases known : (Signature.ofList entries).valueOf? name with
    | none => simp only [advance, known]
    | some body =>
        simp only [advance, known]
        exact expand_eq_of_agreement first second body
          (fun dependency occurs => agree dependency ⟨body, known, occurs⟩)
  · rintro name dependency ⟨body, known, occurs⟩
    exact (check_iff_decreases entries).mp ordered name body known dependency occurs
  · exact rank_lt_bound entries

/-- Once its rank is covered, a generated body contains only opaque or
absent constants. Strict dependency decrease rules out the self-loops that
the more general fixed-point conversion qualifier deliberately permits. -/
theorem bodies_opaque (entries : List (DeclName × Entry Head))
    (ordered : check entries = true) (rounds : Nat) :
    ∀ name, rank entries name < rounds →
      ∀ dependency ∈ constantNames (bodies (Signature.ofList entries) rounds name),
        (Signature.ofList entries).valueOf? dependency = none := by
  induction rounds with
  | zero => intro name impossible; omega
  | succ rounds ih =>
      intro name bounded dependency occurs
      cases known : (Signature.ofList entries).valueOf? name with
      | none =>
          simp only [bodies_of_opaque _ _ known, constantNames, List.mem_singleton] at occurs
          subst dependency
          exact known
      | some body =>
          simp only [bodies, advance, known, constantNames_expand] at occurs
          obtain ⟨earlier, inBody, inExpansion⟩ := List.mem_flatMap.mp occurs
          have smaller := (check_iff_decreases entries).mp ordered name body known earlier inBody
          exact ih earlier (by omega) dependency inExpansion

/-- The computed expansion of any open term contains no selected transparent
constants, including inside types, identity terms and dependent binders. -/
theorem expand_opaque (entries : List (DeclName × Entry Head))
    (ordered : check entries = true) {n : Nat} (term : Tm Head n) :
    ∀ dependency ∈ constantNames
      (expand (bodies (Signature.ofList entries) (entries.length + 1)) term),
        (Signature.ofList entries).valueOf? dependency = none := by
  intro dependency occurs
  rw [constantNames_expand] at occurs
  obtain ⟨name, _inTerm, inExpansion⟩ := List.mem_flatMap.mp occurs
  exact bodies_opaque entries ordered (entries.length + 1) name
    (rank_lt_bound entries name) dependency inExpansion

/-- Re-expansion does no syntactic work on an already expanded term. This
is about transparent constants, not beta normalization or type inference. -/
theorem expand_idempotent (entries : List (DeclName × Entry Head))
    (ordered : check entries = true) {n : Nat} (term : Tm Head n) :
    expand (bodies (Signature.ofList entries) (entries.length + 1))
      (expand (bodies (Signature.ofList entries) (entries.length + 1)) term) =
      expand (bodies (Signature.ofList entries) (entries.length + 1)) term := by
  rw [expand_eq_of_agreement _ (fun name => .const name) _ ?_, expand_identity]
  intro name occurs
  exact bodies_of_opaque _ _ (expand_opaque entries ordered term name occurs)

/-- The dependency check computes a sufficient expansion budget. -/
theorem expansion_checked [DecidableEq Head] (entries : List (DeclName × Entry Head))
    (ordered : check entries = true) : Checked.check entries (entries.length + 1) = true :=
  (check_iff_fixed_point entries (entries.length + 1)).mpr (bodies_fixed entries ordered)

/-- Reuse the original conversion qualification with the proved sufficient
budget, so callers of an ordered package need not guess unfolding rounds. -/
def qualification [DecidableEq Head] (base : Rules Head)
    (baseEmpty : base.computation = RootComputation.empty)
    (entries : List (DeclName × Entry Head)) (ordered : check entries = true) :
    Qualification (extendRules base (Signature.ofList entries)) :=
  Checked.qualification base baseEmpty entries (entries.length + 1)
    (expansion_checked entries ordered)

/-- An executable ordered-package qualifier with no budget parameter. -/
def qualify? [DecidableEq Head] (base : Rules Head)
    (baseEmpty : base.computation = RootComputation.empty)
    (entries : List (DeclName × Entry Head)) :
    Option (Qualification (extendRules base (Signature.ofList entries))) :=
  if ordered : check entries = true then
    some (qualification base baseEmpty entries ordered)
  else none

@[simp] theorem qualify_isSome [DecidableEq Head] (base : Rules Head)
    (baseEmpty : base.computation = RootComputation.empty)
    (entries : List (DeclName × Entry Head)) :
    (qualify? base baseEmpty entries).isSome = check entries := by
  unfold qualify?
  split <;> simp_all

/-- Successful ordered qualification returns precisely the expansion computed
by the existing bounded qualifier, not a newly chosen family of bodies. -/
theorem qualify_bodies [DecidableEq Head] (base : Rules Head)
    (baseEmpty : base.computation = RootComputation.empty)
    (entries : List (DeclName × Entry Head))
    {result : Qualification (extendRules base (Signature.ofList entries))}
    (computed : qualify? base baseEmpty entries = some result) :
    result.bodies = bodies (Signature.ofList entries) (entries.length + 1) := by
  unfold qualify? at computed
  split at computed
  · cases computed
    rfl
  · contradiction

end Ordered

#print axioms constants_convert
#print axioms check_definitions
#print axioms check_iff_fixed_point
#print axioms bodies_stable
#print axioms check_stable
#print axioms qualification
#print axioms qualify_bodies
#print axioms conversion_iff
#print axioms steps_preserve
#print axioms Ordered.check_iff_decreases
#print axioms Ordered.bodies_fixed
#print axioms Ordered.bodies_opaque
#print axioms Ordered.expand_opaque
#print axioms Ordered.expand_idempotent
#print axioms Ordered.expansion_checked
#print axioms Ordered.qualification
#print axioms Ordered.qualify_bodies

end ConstantExpansion.Checked
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
