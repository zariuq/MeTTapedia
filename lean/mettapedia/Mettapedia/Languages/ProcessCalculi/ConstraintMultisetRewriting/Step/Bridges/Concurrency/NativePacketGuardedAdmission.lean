import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionObservations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketQueryCuts

/-!
# Concrete region observations of canonical native packet matches

The store is a bag of physical occurrences, the commit one prepared match,
the guards are asked after that match's own tells, the family program is
fixed, and knowledge is one store. Equation checks stay ordinary checks;
none queries, cardinality and exact collect queries use the actual decoded row region.

This is the canonical tagged common image. Query terms have explicit scope
support below. Freshness of arbitrary openings cannot be inferred from an
unguarded rule body that does not mention its query-only variables.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketGuardedAdmission

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open MeTTaCalculus.OccurrenceCommits (Enabled)
open TaggedAssignments (Object Substitution)
open NativePacketStep (Terms Ports packetAction)
open PredicateQueryAdmission (RegionQuery RegionValid)

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}

def ordinary (site : Object S) : Check (Term (signature S site.2.arity) Γ sort) → List (Check (Terms S O Γ sort))
  | .equal left right => [NativePacketQueryView.equationCheck site left right]
  | .predicate _ _ | .count _ _ => []

noncomputable def observed (site : Object S) : Check (Term (signature S site.2.arity) Γ sort) →
    List (RegionQuery (Terms S O Γ sort) (Substitution S) (Ports O))
  | .equal _ _ => []
  | .predicate quantifier pattern => [.predicate quantifier (NativePacketQueryView.region site pattern)]
  | .count pattern number => [.count (NativePacketQueryView.region site pattern) number]

def prepared {s : NativeState S O Γ sort} (firing : LiveFiring s) :=
  (ContextualActivatedStep.prepared s.locals s.state.declarations s.state.occupied firing.selection firing.rule
    (fun occurrence => (s.state.rows occurrence).value)).rule

def body {s : NativeState S O Γ sort} (firing : LiveFiring s) (use : Nat) : RuleInstance (Terms S O Γ sort) :=
  { NativePacketStep.body firing use with
    checks := (prepared firing).checks.flatMap (ordinary (NativePacketStep.useObject s use)) }

noncomputable def questions {s : NativeState S O Γ sort} (firing : LiveFiring s) (use : Nat) :
    List (RegionQuery (Terms S O Γ sort) (Substitution S) (Ports O)) :=
  (prepared firing).checks.flatMap (observed (NativePacketStep.useObject s use)) ++
    firing.patterns.map fun pattern => RegionQuery.exact
      (NativePacketQueryView.region (NativePacketStep.useObject s use) pattern.1) (pattern.2.image Sum.inl)

def queryTerms {s : NativeState S O Γ sort} (firing : LiveFiring s) (use : Nat) : List (Terms S O Γ sort) :=
  (((prepared firing).checks.flatMap RuleSyntax.checkTerms) ++ firing.patterns.map Prod.fst).map
    (fun term => ContextPackets.observation (NativePacketStep.useObject s use) (observe term))

omit [DecidableEq O] in
theorem query_terms_location {s : NativeState S O Γ sort} (firing : LiveFiring s) (use : Nat) :
    ∀ term ∈ queryTerms firing use, NativePacketStep.location term = some (NativePacketStep.useObject s use) := by
  intro term present
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp present
  rfl

theorem problem_eq {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length) :
    (NativePacketStep.selection members[index]).problem (NativePacketRounds.label members)
        (body members[index] (NativePacketRounds.useTag index)) (NativePacketStep.configuration s 0) =
      NativePacketQueryCuts.memberProblem members index := rfl

theorem equation_ask_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length)
    (enabled : Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit)))
    (left right : Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort) :
    (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Entails (NativePacketQueryCuts.memberProblem members index)
        (fun substitution => (NativePacketQueryView.equationCheck (NativePacketStep.useObject s (NativePacketRounds.useTag index)) left right).Holds
          (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) substitution (NativePacketRounds.label members) (NativePacketStep.present s)) ↔
      (Frames.contextual S).Entails (a := s.infoFrame) (FamilyInformation.memberInformation members[index])
        (fun _ candidate => instantiate candidate left = instantiate candidate right) := by
  have bridge := NativePacketQueryCuts.member_entails_iff members index enabled
    (fun _ candidate => instantiate candidate left = instantiate candidate right)
  constructor
  · intro asked
    apply bridge.mp
    intro substitution model
    exact (NativePacketQueryView.equation_check_iff _ _ _ _ _ _).mp (asked substitution model)
  · intro asked substitution model
    exact (NativePacketQueryView.equation_check_iff _ _ _ _ _ _).mpr (bridge.mpr asked substitution model)

theorem count_ask_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length)
    (enabled : Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit)))
    (pattern : Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort) (number : Nat) :
    (RegionQuery.count (NativePacketQueryView.region (NativePacketStep.useObject s (NativePacketRounds.useTag index)) pattern) number).Ask
        (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (NativePacketQueryCuts.memberProblem members index)
        (NativePacketRounds.label members) (NativePacketStep.present s) ↔
      (Frames.contextual S).Entails (a := s.infoFrame) (FamilyInformation.memberInformation members[index])
        (fun _ candidate => ContextualConditionalGuards.Holds s.locals candidate
          (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present (.count pattern number)) :=
  NativePacketQueryCuts.member_count_ask_iff members index enabled pattern number

/-- A predicate query asked at a member's problem is the check asked at every solution of the
member's information. -/
theorem predicate_ask_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length)
    (enabled : Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit)))
    (quantifier : Quantifier)
    (pattern : Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort) :
    (RegionQuery.predicate quantifier
        (NativePacketQueryView.region (NativePacketStep.useObject s (NativePacketRounds.useTag index)) pattern)).Ask
        (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (NativePacketQueryCuts.memberProblem members index)
        (NativePacketRounds.label members) (NativePacketStep.present s) ↔
      (Frames.contextual S).Entails (a := s.infoFrame) (FamilyInformation.memberInformation members[index])
        (fun _ candidate => ContextualConditionalGuards.Holds s.locals candidate
          (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present
          (.predicate quantifier pattern)) := by
  have point (substitution : Substitution S)
      (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
        (NativePacketQueryCuts.memberProblem members index)) :
      (RegionQuery.predicate quantifier
          (NativePacketQueryView.region (NativePacketStep.useObject s (NativePacketRounds.useTag index)) pattern)).Holds
          substitution (NativePacketRounds.label members) (NativePacketStep.present s) ↔
        ContextualConditionalGuards.Holds s.locals
          (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag index))).2
          (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present
          (.predicate quantifier pattern) := by
    refine Iff.trans ?_ (NativeResidual.predicate_iff_region _ _ _ quantifier pattern).symm
    change quantifier.Accepts (MeTTaCalculus.OccurrenceCommits.regionOf _ _ (NativePacketQueryView.region _ _ _)) ↔ _
    rw [NativePacketQueryCuts.member_region members index enabled substitution model pattern]
    cases quantifier with
    | any => exact Finset.image_nonempty
    | none => exact Finset.image_eq_empty
  have bridge := NativePacketQueryCuts.member_entails_iff members index enabled
    (fun _ candidate => ContextualConditionalGuards.Holds s.locals candidate
      (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present
      (.predicate quantifier pattern))
  constructor
  · intro asked
    exact bridge.mp (fun substitution model => (point substitution model).mp (asked substitution model))
  · intro asked substitution model
    exact (point substitution model).mpr (bridge.mpr asked substitution model)

theorem none_ask_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length)
    (enabled : Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit)))
    (pattern : Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort) :
    (RegionQuery.predicate .none (NativePacketQueryView.region (NativePacketStep.useObject s (NativePacketRounds.useTag index)) pattern)).Ask
        (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (NativePacketQueryCuts.memberProblem members index)
        (NativePacketRounds.label members) (NativePacketStep.present s) ↔
      (Frames.contextual S).Entails (a := s.infoFrame) (FamilyInformation.memberInformation members[index])
        (fun _ candidate => ContextualConditionalGuards.Holds s.locals candidate
          (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present (.predicate .none pattern)) :=
  predicate_ask_iff members index enabled .none pattern

theorem exact_ask_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length)
    (enabled : Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit)))
    (pattern : Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort) (seen : Finset O) :
    (RegionQuery.exact (NativePacketQueryView.region (NativePacketStep.useObject s (NativePacketRounds.useTag index)) pattern)
        (seen.image Sum.inl)).Ask (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
        (NativePacketQueryCuts.memberProblem members index) (NativePacketRounds.label members) (NativePacketStep.present s) ↔
      (Frames.contextual S).Entails (a := s.infoFrame) (FamilyInformation.memberInformation members[index])
        (fun _ candidate => ContextualConditionalGuards.region s.locals candidate
          (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present pattern = seen) :=
  NativePacketQueryCuts.member_exact_ask_iff members index enabled pattern seen

theorem check_asks_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length)
    (enabled : Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit)))
    (check : Check (Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort)) :
    ((∀ compiled ∈ ordinary (NativePacketStep.useObject s (NativePacketRounds.useTag index)) check,
        (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Entails (NativePacketQueryCuts.memberProblem members index)
          (fun substitution => compiled.Holds (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) substitution
            (NativePacketRounds.label members) (NativePacketStep.present s))) ∧
      ∀ query ∈ observed (NativePacketStep.useObject s (NativePacketRounds.useTag index)) check,
        query.Ask (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (NativePacketQueryCuts.memberProblem members index)
          (NativePacketRounds.label members) (NativePacketStep.present s)) ↔
      (Frames.contextual S).Entails (a := s.infoFrame) (FamilyInformation.memberInformation members[index])
        (fun _ candidate => ContextualConditionalGuards.Holds s.locals candidate
          (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present check) := by
  cases check with
  | equal left right =>
      constructor
      · intro asked target candidate model
        exact (equation_ask_iff members index enabled left right).mp
          (asked.1 _ List.mem_cons_self) target candidate model
      · intro asked
        refine ⟨?_,fun _ inside => absurd inside List.not_mem_nil⟩
        intro compiled inside
        obtain rfl := List.mem_singleton.mp inside
        exact (equation_ask_iff members index enabled left right).mpr asked
  | predicate quantifier pattern =>
      constructor
      · intro asked
        exact (predicate_ask_iff members index enabled quantifier pattern).mp (asked.2 _ List.mem_cons_self)
      · intro asked
        refine ⟨fun _ inside => absurd inside List.not_mem_nil,?_⟩
        intro query inside
        obtain rfl := List.mem_singleton.mp inside
        exact (predicate_ask_iff members index enabled quantifier pattern).mpr asked
  | count pattern number =>
      constructor
      · intro asked
        exact (count_ask_iff members index enabled pattern number).mp (asked.2 _ List.mem_cons_self)
      · intro asked
        refine ⟨fun _ inside => absurd inside List.not_mem_nil,?_⟩
        intro query inside
        obtain rfl := List.mem_singleton.mp inside
        exact (count_ask_iff members index enabled pattern number).mpr asked

theorem asks_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length)
    (enabled : Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit))) :
    ((∀ check ∈ (body members[index] (NativePacketRounds.useTag index)).checks,
        (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Entails (NativePacketQueryCuts.memberProblem members index)
          (fun substitution => check.Holds (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) substitution
            (NativePacketRounds.label members) (NativePacketStep.present s))) ∧
      ∀ query ∈ questions members[index] (NativePacketRounds.useTag index),
        query.Ask (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (NativePacketQueryCuts.memberProblem members index)
          (NativePacketRounds.label members) (NativePacketStep.present s)) ↔
      ((∀ check ∈ (prepared members[index]).checks,
          (Frames.contextual S).Entails (a := s.infoFrame) (FamilyInformation.memberInformation members[index])
            (fun _ candidate => ContextualConditionalGuards.Holds s.locals candidate
              (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present check)) ∧
        ∀ pattern ∈ members[index].patterns,
          (Frames.contextual S).Entails (a := s.infoFrame) (FamilyInformation.memberInformation members[index])
            (fun _ candidate => ContextualConditionalGuards.region s.locals candidate
              (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present pattern.1 = pattern.2)) := by
  constructor
  · rintro ⟨ordinaryAll,observedAll⟩
    refine ⟨?_,?_⟩
    · intro check inside
      apply (check_asks_iff members index enabled check).mp
      exact ⟨fun compiled member => ordinaryAll compiled (List.mem_flatMap.mpr ⟨check,inside,member⟩),
        fun query member => observedAll query (List.mem_append_left _ (List.mem_flatMap.mpr ⟨check,inside,member⟩))⟩
    · intro pattern inside
      apply (exact_ask_iff members index enabled pattern.1 pattern.2).mp
      exact observedAll _ (List.mem_append_right _ (List.mem_map.mpr ⟨pattern,inside,rfl⟩))
  · rintro ⟨checks,patterns⟩
    refine ⟨?_,?_⟩
    · intro compiled inside
      obtain ⟨check,member,inside⟩ := List.mem_flatMap.mp inside
      exact ((check_asks_iff members index enabled check).mpr (checks check member)).1 compiled inside
    · intro query inside
      rcases List.mem_append.mp inside with guarded | patterned
      · obtain ⟨check,member,inside⟩ := List.mem_flatMap.mp guarded
        exact ((check_asks_iff members index enabled check).mpr (checks check member)).2 query inside
      · obtain ⟨pattern,member,rfl⟩ := List.mem_map.mp patterned
        exact (exact_ask_iff members index enabled pattern.1 pattern.2).mpr (patterns pattern member)

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

theorem native_asks_iff {s : NativeState S O Γ sort} (firing : LiveFiring s) :
    (Frames.contextual S).Entails (a := s.infoFrame) (FamilyInformation.memberInformation firing) (native.Holds firing.toNative) ↔
      ((∀ check ∈ (prepared firing).checks,
          (Frames.contextual S).Entails (a := s.infoFrame) (FamilyInformation.memberInformation firing)
            (fun _ candidate => ContextualConditionalGuards.Holds s.locals candidate
              (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present check)) ∧
        ∀ pattern ∈ firing.patterns,
          (Frames.contextual S).Entails (a := s.infoFrame) (FamilyInformation.memberInformation firing)
            (fun _ candidate => ContextualConditionalGuards.region s.locals candidate
              (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present pattern.1 = pattern.2)) := by
  constructor
  · intro asked
    refine ⟨fun check inside target candidate model => (asked target candidate model).1 check inside,?_⟩
    intro pattern inside target candidate model
    exact (ContextualPredicateQueryAdmission.matching_holds_iff s.locals pattern.1 pattern.2
      (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present
      ⟨target.Names,target.arity,candidate⟩).mp
        ((asked target candidate model).2 _ (List.mem_map.mpr ⟨pattern,inside,rfl⟩))
  · rintro ⟨checks,patterns⟩ target candidate model
    refine ⟨fun check inside => checks check inside target candidate model,?_⟩
    intro query inside
    change query ∈ firing.patterns.map _ at inside
    obtain ⟨pattern,member,rfl⟩ := List.mem_map.mp inside
    exact (ContextualPredicateQueryAdmission.matching_holds_iff s.locals pattern.1 pattern.2
      (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present
      ⟨target.Names,target.arity,candidate⟩).mpr (patterns pattern member target candidate model)

theorem regionValid_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length)
    (shapes : native.Shapes members[index].toNative) :
    RegionValid (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (NativePacketRounds.label members)
        (body members[index] (NativePacketRounds.useTag index)) (questions members[index] (NativePacketRounds.useTag index))
        (NativePacketStep.configuration s 0) (NativePacketStep.selection members[index]) ↔
      members[index].toNative.Realized ∧
        (NativePacketStep.selection members[index]).made.map (NativePacketRounds.label members) =
          (NativePacketStep.body members[index] (NativePacketRounds.useTag index)).produce := by
  constructor
  · intro valid
    have packetEnabled : Enabled (fun _ : Ports O => ()) (NativePacketStep.present s)
        ((NativePacketStep.selection members[index]).commit (T := Unit)) :=
      ⟨valid.firing.occurrences.taken_subset,valid.firing.occurrences.kept_subset,valid.firing.occurrences.apart,
        valid.firing.occurrences.fresh,fun _ inside => by simp [Selection.commit] at inside⟩
    have enabled := (NativePacketStep.selection_enabled members[index]).mp packetEnabled
    have actualAsks := (native_asks_iff members[index]).mpr
      ((asks_iff members index enabled).mp ⟨valid.firing.checks,valid.observations⟩)
    obtain ⟨substitution,model⟩ := valid.firing.consistent
    rw [problem_eq] at model
    have info := (NativePacketQueryCuts.member_models_iff members index enabled substitution).mp model
    refine ⟨(native_admits_iff members[index].toNative).mpr ⟨shapes,enabled,?_,actualAsks⟩,valid.firing.outputs⟩
    exact ⟨(substitution (NativePacketStep.useObject s (NativePacketRounds.useTag index))).1.2,
      (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag index))).2,info.1⟩
  · rintro ⟨realized,keeps⟩
    have source := (native_admits_iff members[index].toNative).mp realized
    have enabled := source.2.1
    have packetEnabled := (NativePacketStep.selection_enabled members[index]).mpr enabled
    have actualAsks := (asks_iff members index enabled).mpr ((native_asks_iff members[index]).mp source.2.2.2)
    refine ⟨⟨?_,?_,?_,?_,keeps,?_,?_,actualAsks.1⟩,actualAsks.2⟩
    · exact shapes.1.map Sum.inl_injective
    · exact shapes.2.1.map Sum.inl_injective
    · simp [body,NativePacketStep.body,NativePacketStep.selection]
    · simp [body,NativePacketStep.body,NativePacketStep.selection]
    · exact ⟨packetEnabled.taken_subset,packetEnabled.kept_subset,packetEnabled.apart,packetEnabled.fresh,
        fun _ inside => by simp [Selection.commit] at inside⟩
    · obtain ⟨target,candidate,model⟩ := source.2.2.1
      rw [problem_eq]
      exact ⟨NativePacketStep.fit s 0 (NativePacketRounds.useTag index) target candidate,
        NativePacketQueryCuts.member_fit_model members index enabled target candidate model⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketGuardedAdmission
