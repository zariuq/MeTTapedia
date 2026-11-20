import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketGuardedAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.PacketJointFreshness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ObservedBags

/-!
# Scoped query code for the finite canonical packet program

The store is a bag of physical occurrences, the commit is a bag of matches,
each guard is asked after that member's own tells, the program is fixed,
and knowledge is one store. Query code records none queries, cardinality or an
exact occurrence set. Its patterns are actual opened observation packets.
The decoder consumes their target frame and contextual term, and the row's
actual schema and capture assignment. Malformed scope lengths explicitly
reject; no guard is discarded.

Canonical joint freshness includes these query patterns. Admission of an
own-guard bag does not assert pairwise query blindness or serializability.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketScopedQueries

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open TaggedAssignments (Object Substitution)
open ContextPackets (Value)
open NativePacketStep (Terms Ports packetAction)
open PredicateQueryAdmission (RegionQuery)
open RuleSyntax.StepWeb.ObservedBags

variable {S : Signature} {O : Type} {Γ : Ctx S} {sort : S.Srt}

def decodedMatches (patternValue rowValue : Terms S O Γ sort) : Prop :=
  ∃ (target : Object S) (pattern : Term (signature S target.2.arity) Γ sort),
    patternValue = ContextPackets.observation target (observe pattern) ∧
      NativePacketQueryView.MatchesAt target pattern rowValue

theorem decodedMatches_observation (target : Object S)
    (pattern : Term (signature S target.2.arity) Γ sort) (rowValue : Terms S O Γ sort) :
    decodedMatches (ContextPackets.observation target (observe pattern)) rowValue ↔
      NativePacketQueryView.MatchesAt target pattern rowValue := by
  constructor
  · rintro ⟨other,otherPattern,equal,matched⟩
    have packed := Value.observation.inj equal
    have sameTarget : target = other := congrArg (fun value : TaggedAssignments.Packed S => value.1) packed
    subst other
    have samePattern : pattern = otherPattern := observe_injective (TaggedAssignments.pack_injective target packed)
    subst otherPattern
    exact matched
  · intro matched
    exact ⟨target,pattern,rfl,matched⟩

noncomputable def decodedRegion (patternValue : Terms S O Γ sort)
    (substitution : Substitution S) (rowValue : Terms S O Γ sort) : Bool := by
  classical
  exact decide (decodedMatches (ContextPackets.apply S substitution patternValue)
    (ContextPackets.apply S substitution rowValue))

theorem decodedRegion_observation (target : Object S)
    (pattern : Term (signature S target.2.arity) Γ sort) :
    decodedRegion (O := O) (ContextPackets.observation target (observe pattern)) =
      NativePacketQueryView.region target pattern := by
  classical
  funext substitution rowValue
  change decide (decodedMatches
      (ContextPackets.observation (substitution target).1 (observe (instantiate (substitution target).2 pattern)))
      (ContextPackets.apply S substitution rowValue)) =
    decide (NativePacketQueryView.MatchesAt (substitution target).1
      (instantiate (substitution target).2 pattern) (ContextPackets.apply S substitution rowValue))
  exact congrArg (fun proposition : Prop => decide proposition)
    (propext (decodedMatches_observation _ _ _))

theorem decodedRegion_compose (patternValue rowValue : Terms S O Γ sort) (outer inner : Substitution S) :
    decodedRegion patternValue (TaggedAssignments.compose S outer inner) rowValue =
      decodedRegion (ContextPackets.apply S inner patternValue) outer (ContextPackets.apply S inner rowValue) := by
  have patternApplied : ContextPackets.apply S (TaggedAssignments.compose S outer inner) patternValue =
      ContextPackets.apply S outer (ContextPackets.apply S inner patternValue) :=
    (ContextPackets.action S (NativePacketStep.Rigid S O Γ sort)).apply_compose outer inner patternValue
  have rowApplied : ContextPackets.apply S (TaggedAssignments.compose S outer inner) rowValue =
      ContextPackets.apply S outer (ContextPackets.apply S inner rowValue) :=
    (ContextPackets.action S (NativePacketStep.Rigid S O Γ sort)).apply_compose outer inner rowValue
  unfold decodedRegion
  rw [patternApplied,rowApplied]

inductive QueryCode (O : Type) where
  | predicate (quantifier : Quantifier)
  | count (number : Nat)
  | exact (seen : Finset (Ports O))

noncomputable def query (code : QueryCode O) (patternValue : Terms S O Γ sort) :
    RegionQuery (Terms S O Γ sort) (Substitution S) (Ports O) :=
  match code with
  | .predicate q => .predicate q (decodedRegion patternValue)
  | .count number => .count (decodedRegion patternValue) number
  | .exact seen => .exact (decodedRegion patternValue) seen

def reject : RegionQuery (Terms S O Γ sort) (Substitution S) (Ports O) where
  region _ _ := false
  accepts _ _ := False

theorem reject_never_holds (substitution : Substitution S) (label : Ports O → Terms S O Γ sort)
    (world : Finset (Ports O)) : ¬ (reject (S := S)).Holds substitution label world := by
  intro impossible
  exact impossible

noncomputable def decode : List (QueryCode O) → List (Terms S O Γ sort) →
    List (RegionQuery (Terms S O Γ sort) (Substitution S) (Ports O))
  | [],[] => []
  | code :: rest,patternValue :: patterns => query code patternValue :: decode rest patterns
  | _,_ => [reject]

theorem decode_bad_length (codes : List (QueryCode O)) (patterns : List (Terms S O Γ sort))
    (different : codes.length ≠ patterns.length) : reject ∈ decode codes patterns := by
  induction codes generalizing patterns with
  | nil =>
      cases patterns with
      | nil => exact (different rfl).elim
      | cons pattern rest => exact List.mem_singleton_self _
  | cons code rest ih =>
      cases patterns with
      | nil => exact List.mem_singleton_self _
      | cons pattern patterns =>
          exact List.mem_cons_of_mem _ (ih patterns (fun same => different (congrArg Nat.succ same)))

def checkPlan {T : Type} : Check T → List (QueryCode O × T)
  | .equal _ _ => []
  | .predicate q pattern => [(.predicate q,pattern)]
  | .count pattern number => [(.count number,pattern)]

variable [DecidableEq O]

def plan {s : NativeState S O Γ sort} (firing : LiveFiring s) :
    List (QueryCode O × Term (signature S s.infoFrame.arity) Γ sort) :=
  (NativePacketGuardedAdmission.prepared firing).checks.flatMap checkPlan ++
    firing.patterns.map fun pattern => (.exact (pattern.2.image Sum.inl),pattern.1)

def codes {s : NativeState S O Γ sort} (firing : LiveFiring s) : List (QueryCode O) :=
  (plan firing).map Prod.fst

def scopeTerms {s : NativeState S O Γ sort} (firing : LiveFiring s) (use : Nat) : List (Terms S O Γ sort) :=
  (plan firing).map fun entry => ContextPackets.observation (NativePacketStep.useObject s use) (observe entry.2)

theorem scope_terms_location {s : NativeState S O Γ sort} (firing : LiveFiring s) (use : Nat) :
    ∀ term ∈ scopeTerms firing use, NativePacketStep.location term = some (NativePacketStep.useObject s use) := by
  intro term inside
  obtain ⟨entry,_,rfl⟩ := List.mem_map.mp inside
  rfl

theorem scope_length {s : NativeState S O Γ sort} (firing : LiveFiring s) (use : Nat) :
    (codes firing).length = (scopeTerms firing use).length := by simp [codes,scopeTerms]

omit [DecidableEq O] in
theorem decode_plan (site : Object S)
    (entries : List (QueryCode O × Term (signature S site.2.arity) Γ sort)) :
    decode (Γ := Γ) (sort := sort) (entries.map Prod.fst) (entries.map fun entry => ContextPackets.observation site (observe entry.2)) =
      entries.map fun entry => query (Γ := Γ) (sort := sort) entry.1 (ContextPackets.observation site (observe entry.2)) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => simp only [List.map_cons,decode,ih]

omit [DecidableEq O] in
theorem check_queries (site : Object S) (check : Check (Term (signature S site.2.arity) Γ sort)) :
    (checkPlan (O := O) check).map (fun entry => query (Γ := Γ) (sort := sort) entry.1 (ContextPackets.observation site (observe entry.2))) =
      NativePacketGuardedAdmission.observed site check := by
  cases check <;> simp only [checkPlan,List.map_nil,List.map_cons,query,
    decodedRegion_observation,NativePacketGuardedAdmission.observed]

omit [DecidableEq O] in
theorem checks_queries (site : Object S) (checks : List (Check (Term (signature S site.2.arity) Γ sort))) :
    (checks.flatMap (checkPlan (O := O))).map
        (fun entry => query (Γ := Γ) (sort := sort) entry.1 (ContextPackets.observation site (observe entry.2))) =
      checks.flatMap (NativePacketGuardedAdmission.observed site) := by
  induction checks with
  | nil => rfl
  | cons check rest ih => rw [List.flatMap_cons,List.map_append,check_queries,ih,List.flatMap_cons]

theorem canonical_queries {s : NativeState S O Γ sort} (firing : LiveFiring s) (use : Nat) :
    decode (codes firing) (scopeTerms firing use) = NativePacketGuardedAdmission.questions firing use := by
  have decoded : decode (codes firing) (scopeTerms firing use) =
      (plan firing).map (fun entry => query entry.1
        (ContextPackets.observation (NativePacketStep.useObject s use) (observe entry.2))) :=
    decode_plan (NativePacketStep.useObject s use) (plan firing)
  rw [decoded]
  dsimp only [NativePacketStep.useObject] at *
  unfold plan NativePacketGuardedAdmission.questions
  dsimp only [NativePacketStep.useObject,NativeState.infoFrame,ContextualActivatedStep.target] at *
  rw [List.map_append]
  have checkMap := checks_queries (O := O) (Γ := Γ) (sort := sort)
    (NativePacketStep.useObject s use) (NativePacketGuardedAdmission.prepared firing).checks
  dsimp only [NativePacketStep.useObject,NativeState.infoFrame,ContextualActivatedStep.target] at checkMap
  rw [checkMap,List.map_map]
  congr 1
  apply List.map_congr_left
  intro entry _
  simp only [Function.comp_apply,query]
  exact congrArg (fun region => RegionQuery.exact region (entry.2.image Sum.inl))
    (decodedRegion_observation (O := O) (NativePacketStep.useObject s use) entry.1)

def rule {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length) :
    RuleSyntax.Rule (RuleSyntax.OneFrame.Terms (Terms S O Γ sort)) :=
  ⟨PUnit.unit,NativePacketGuardedAdmission.body members[index] (NativePacketRounds.useTag index),[]⟩

def program {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :
    RuleSyntax.Program (RuleSyntax.OneFrame.Terms (Terms S O Γ sort)) := Set.range (rule members)

omit [DecidableEq O] in
theorem program_finite {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :
    (program members).Finite := Set.finite_range _

omit [DecidableEq O] in
theorem rule_injective {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :
    Function.Injective (rule members) := by
  intro first second equal
  let finalRead : RuleSyntax.Rule (RuleSyntax.OneFrame.Terms (Terms S O Γ sort)) → Option (Terms S O Γ sort)
    | ⟨PUnit.unit,body,_⟩ => body.read.getLast?
  have last := congrArg finalRead equal
  have captureEqual :
      NativePacketStep.captureRow s (NativePacketRounds.useTag first) =
        NativePacketStep.captureRow s (NativePacketRounds.useTag second) := by
    apply Option.some.inj
    simpa [finalRead,rule,NativePacketGuardedAdmission.body,NativePacketStep.body] using last
  have sites := congrArg (NativePacketStep.location (S := S) (O := O) (Γ := Γ) (sort := sort)) captureEqual
  change some (NativePacketStep.useObject s (NativePacketRounds.useTag first)) =
    some (NativePacketStep.useObject s (NativePacketRounds.useTag second)) at sites
  have tags := congrArg Prod.fst (Option.some.inj sites)
  apply Fin.ext
  dsimp [NativePacketRounds.useTag,NativePacketStep.useObject] at tags
  omega

noncomputable def indexOf {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (raw : RuleSyntax.Rule (RuleSyntax.OneFrame.Terms (Terms S O Γ sort))) (inside : raw ∈ program members) :
    Fin members.length := Classical.choose inside

omit [DecidableEq O] in
theorem indexOf_spec {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (raw : RuleSyntax.Rule (RuleSyntax.OneFrame.Terms (Terms S O Γ sort))) (inside : raw ∈ program members) :
    rule members (indexOf members raw inside) = raw := Classical.choose_spec inside

omit [DecidableEq O] in
theorem indexOf_rule {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length)
    (inside : rule members index ∈ program members) : indexOf members (rule members index) inside = index :=
  rule_injective members (indexOf_spec members (rule members index) inside)

def liftQuery (query : RegionQuery (Terms S O Γ sort) (Substitution S) (Ports O)) :
    RegionQuery (Terms S O Γ sort) (Σ _ : PUnit, Substitution S) (Ports O) where
  region solution := query.region solution.2
  accepts solution := query.accepts solution.2

noncomputable def scopedQueries {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :
    ScopedQueries (RuleSyntax.OneFrame.Terms (Terms S O Γ sort)) (Ports O)
      (RuleSyntax.OneFrame.ext (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (program members) where
  scope raw inside := scopeTerms members[indexOf members raw inside] (NativePacketRounds.useTag (indexOf members raw inside))
  build raw inside values := (decode (codes members[indexOf members raw inside]) values).map liftQuery

def member {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length) :
    RuleSyntax.JointFirings.OneMember (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (Ports O)
      (program members) where
  rule := rule members index
  member := ⟨index,rfl⟩
  opening := TaggedAssignments.identity S
  selection := NativePacketStep.selection members[index]
  seen := []

def memberList {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :=
  (List.finRange members.length).map (member members)

omit [DecidableEq O] in
theorem member_opened {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length) :
    (member members index).firing.opened
        (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) =
      NativePacketGuardedAdmission.body members[index] (NativePacketRounds.useTag index) := by
  change (NativePacketGuardedAdmission.body members[index] (NativePacketRounds.useTag index)).map
    ((ContextPackets.action S (NativePacketStep.Rigid S O Γ sort)).apply (TaggedAssignments.identity S)) = _
  have identity : (ContextPackets.action S (NativePacketStep.Rigid S O Γ sort)).apply (TaggedAssignments.identity S) = id :=
    funext (ContextPackets.action S (NativePacketStep.Rigid S O Γ sort)).apply_identity
  have checkIdentity : Check.map (id : Terms S O Γ sort → Terms S O Γ sort) = id := by
    funext check
    cases check <;> rfl
  have pairIdentity : (fun pair : Terms S O Γ sort × Terms S O Γ sort => (id pair.1,id pair.2)) = id := by
    funext pair
    cases pair
    rfl
  rw [identity]
  simp only [RuleInstance.map,checkIdentity,pairIdentity,List.map_id]

theorem member_information {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length) :
    (member members index).firing.information
        (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
        (NativePacketRounds.source members) = NativePacketQueryCuts.memberProblem members index := by
  have information := RuleSyntax.OneFrame.information_eq (A := packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
    (label := NativePacketRounds.label members) (NativePacketStep.configuration s 0) (member members index).firing
  have opened := congrArg
    (fun openedBody => (NativePacketStep.selection members[index]).problem (NativePacketRounds.label members)
      openedBody (NativePacketStep.configuration s 0)) (member_opened members index)
  exact information.trans (opened.trans (NativePacketGuardedAdmission.problem_eq members index))

theorem member_row {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length) :
    (member members index).firing.row
        (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
        (NativePacketRounds.source members) = NativePacketRounds.label members :=
  RuleSyntax.OneFrame.row_eq (A := packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
    (label := NativePacketRounds.label members) (NativePacketStep.configuration s 0) (member members index).firing

theorem joint_information {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :
    (RuleSyntax.JointFirings.bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (memberList members)).information
        (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
        (NativePacketRounds.source members) = NativePacketRounds.jointProblem members := by
  have information := RuleSyntax.StepWeb.Rounds.information_embed
    (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
    (NativePacketRounds.label members) (NativePacketStep.configuration s 0) (memberList members)
  apply information.trans
  unfold NativePacketRounds.jointProblem AnnotatedRuns.jointProblem
  rw [NativePacketRounds.image_as_indices]
  simp only [memberList,RuleSyntax.StepWeb.Rounds.image,List.flatMap_map]
  have added (index : Fin members.length) :
      (RuleSyntax.StepWeb.Rounds.baseFiring (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
        (member members index)).added (NativePacketRounds.label members) =
        (NativePacketStep.baseFiring members[index] (NativePacketRounds.useTag index)).added
          (NativePacketRounds.label members) := by
    have opened := congrArg
      (fun openedBody => GuardFreeProcessOrders.added (NativePacketRounds.label members)
        openedBody (NativePacketStep.selection members[index])) (member_opened members index)
    exact opened.trans rfl
  exact congrArg (List.append (NativePacketStep.configuration s 0).equations)
    (List.flatMap_congr fun index _ => added index)

theorem canonical_scope {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length) :
    (scopedQueries members).scope (member members index).rule (member members index).member =
      scopeTerms members[index] (NativePacketRounds.useTag index) := by
  change scopeTerms members[indexOf members (rule members index) _]
    (NativePacketRounds.useTag (indexOf members (rule members index) _)) = _
  exact congrArg (fun chosen : Fin members.length => scopeTerms members[chosen] (NativePacketRounds.useTag chosen))
    (indexOf_rule members index ⟨index,rfl⟩)

theorem canonical_profile {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length) :
    (scopedQueries members).profile
        (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (member members index) =
      (NativePacketGuardedAdmission.questions members[index] (NativePacketRounds.useTag index)).map liftQuery := by
  unfold ScopedQueries.profile
  change (decode (codes members[indexOf members (rule members index) _])
    ((scopeTerms members[indexOf members (rule members index) _]
      (NativePacketRounds.useTag (indexOf members (rule members index) _))).map
      (ContextPackets.apply S (TaggedAssignments.identity S)))).map liftQuery = _
  have chosen := indexOf_rule members index (show rule members index ∈ program members from ⟨index,rfl⟩)
  have atIndex := congrArg (fun chosen : Fin members.length =>
    (decode (codes members[chosen]) ((scopeTerms members[chosen] (NativePacketRounds.useTag chosen)).map
      (ContextPackets.apply S (TaggedAssignments.identity S)))).map liftQuery) chosen
  apply atIndex.trans
  have fixed : (scopeTerms members[index] (NativePacketRounds.useTag index)).map
      (ContextPackets.apply S (TaggedAssignments.identity S)) = scopeTerms members[index] (NativePacketRounds.useTag index) := by
    exact List.map_id'' (fun value => (ContextPackets.action S (NativePacketStep.Rigid S O Γ sort)).apply_identity value) _
  rw [fixed,canonical_queries]

theorem member_questions_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length) :
    (∀ query ∈ (scopedQueries members).profile
        (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (member members index),
      (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))).Entails
        ((member members index).firing.information
          (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
          (NativePacketRounds.source members))
        (fun target substitution => query.Holds ⟨target,substitution⟩
          ((member members index).firing.row
            (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
            (NativePacketRounds.source members)) (NativePacketRounds.source members).present)) ↔
      ∀ query ∈ NativePacketGuardedAdmission.questions members[index] (NativePacketRounds.useTag index),
        query.Ask (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
          (NativePacketQueryCuts.memberProblem members index) (NativePacketRounds.label members) (NativePacketStep.present s) := by
  rw [canonical_profile,member_information,member_row]
  constructor
  · intro asked query inside substitution model
    exact asked (liftQuery query) (List.mem_map.mpr ⟨query,inside,rfl⟩) PUnit.unit substitution model
  · intro asked query inside target substitution model
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp inside
    exact asked original member substitution model

theorem asksOwn_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :
    AsksOwn (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
        ((scopedQueries members).profile
          (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))))
        (s := NativePacketRounds.source members)
        (RuleSyntax.JointFirings.bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (memberList members)) ↔
      ∀ index : Fin members.length,
        ∀ query ∈ NativePacketGuardedAdmission.questions members[index] (NativePacketRounds.useTag index),
          query.Ask (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
            (NativePacketQueryCuts.memberProblem members index) (NativePacketRounds.label members) (NativePacketStep.present s) := by
  constructor
  · intro asked index
    apply (member_questions_iff members index).mp
    exact asked _ (List.mem_map.mpr ⟨index,List.mem_finRange index,rfl⟩)
  · intro asked selected inside
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp inside
    exact (member_questions_iff members index).mpr (asked index)

omit [DecidableEq O] in
theorem ordinary_terms_location (site : Object S)
    (check : Check (Term (signature S site.2.arity) Γ sort)) :
    ∀ compiled ∈ NativePacketGuardedAdmission.ordinary (O := O) site check,
      ∀ term ∈ RuleSyntax.checkTerms compiled, NativePacketStep.location term = some site := by
  cases check with
  | equal left right =>
      intro compiled inside term mentioned
      obtain rfl := List.mem_singleton.mp inside
      simp only [NativePacketQueryView.equationCheck,RuleSyntax.checkTerms,List.mem_cons,List.not_mem_nil,or_false] at mentioned
      rcases mentioned with rfl | rfl <;> rfl
  | predicate quantifier pattern => intro _ inside; cases inside
  | count pattern number => intro _ inside; cases inside

omit [DecidableEq O] in
theorem rule_terms_location {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length) :
    ∀ term ∈ (rule members index).terms,
      NativePacketStep.location term = some (NativePacketStep.useObject s (NativePacketRounds.useTag index)) := by
  intro term inside
  by_cases checked : term ∈ ((NativePacketGuardedAdmission.prepared members[index]).checks.flatMap
      (NativePacketGuardedAdmission.ordinary (O := O) (NativePacketStep.useObject s (NativePacketRounds.useTag index)))).flatMap RuleSyntax.checkTerms
  · obtain ⟨compiled,guarded,mentioned⟩ := List.mem_flatMap.mp checked
    obtain ⟨check,_,compiledIn⟩ := List.mem_flatMap.mp guarded
    exact ordinary_terms_location _ check compiled compiledIn term mentioned
  · apply NativePacketStep.rule_location members[index] (NativePacketRounds.useTag index) term
    have emptyChecks : (NativePacketStep.body members[index] (NativePacketRounds.useTag index)).checks = [] := rfl
    simpa only [rule,RuleSyntax.Rule.terms,NativePacketGuardedAdmission.body,NativePacketStep.rule,
      emptyChecks,List.mem_append,List.flatMap_nil,List.not_mem_nil,or_false,checked] using inside

theorem realizedOn_mono {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (selected : List (RuleSyntax.JointFirings.OneMember
      (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (Ports O) (program members)))
    (Q R : Substitution S → Prop) (monotone : ∀ substitution, Q substitution → R substitution) :
    RealizedOn (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
        (scopedQueries members).scope PUnit.unit selected Q →
      RealizedOn (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
        (scopedQueries members).scope PUnit.unit selected R := by
  induction selected generalizing Q R with
  | nil =>
      rintro ⟨substitution,satisfied⟩
      exact ⟨substitution,monotone substitution satisfied⟩
  | cons selected rest ih =>
      intro realized wanted
      let P (substitution : Substitution S) : Prop :=
        ∀ term ∈ selected.rule.terms ++ (scopedQueries members).scope selected.rule selected.member,
          ContextPackets.apply S substitution (ContextPackets.apply S selected.opening term) =
            ContextPackets.apply S wanted term
      have later : RealizedOn
          (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
          (scopedQueries members).scope PUnit.unit rest (fun substitution => Q substitution ∧ P substitution) :=
        realized wanted
      have monotoneLater : ∀ substitution, (Q substitution ∧ P substitution) → (R substitution ∧ P substitution) :=
        fun substitution data => ⟨monotone substitution data.1,data.2⟩
      exact ih _ _ monotoneLater later

theorem realizedOn_forget {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (selected : List (RuleSyntax.JointFirings.OneMember
      (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (Ports O) (program members)))
    (Q : Substitution S → Prop) :
    RealizedOn (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
        (scopedQueries members).scope PUnit.unit selected Q →
      RuleSyntax.JointFirings.Realized
        (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) PUnit.unit selected Q := by
  induction selected generalizing Q with
  | nil => exact id
  | cons selected rest ih =>
      intro realized wanted
      have later := ih _ (realized wanted)
      exact RuleSyntax.JointFirings.Realized.mono
        (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) rest
        (fun substitution data => ⟨data.1,fun term inside => data.2 term (List.mem_append_left _ inside)⟩) later

theorem realized_indices {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (incoming : Substitution S) :
    ∀ (indices : List (Fin members.length)), indices.Nodup →
      ∀ requested : Fin members.length → Substitution S,
        RealizedOn
          (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
          (scopedQueries members).scope PUnit.unit (indices.map (member members)) (fun joint =>
            joint (NativePacketStep.baseObject s 0) = incoming (NativePacketStep.baseObject s 0) ∧
              ∀ index, index ∉ indices → joint (NativePacketStep.useObject s (NativePacketRounds.useTag index)) =
                requested index (NativePacketStep.useObject s (NativePacketRounds.useTag index)))
  | [],_,requested => by
      refine ⟨NativePacketRounds.patch s members.length (incoming (NativePacketStep.baseObject s 0))
        (fun index => requested index (NativePacketStep.useObject s (NativePacketRounds.useTag index))),?_,?_⟩
      · exact NativePacketRounds.patch_base _ _ _ _
      · intro index _
        exact NativePacketRounds.patch_use _ _ _ _ index
  | index :: rest,distinct,requested => by
      intro wanted
      have parts := List.nodup_cons.mp distinct
      have later := realized_indices members incoming rest parts.2 (Function.update requested index wanted)
      refine realizedOn_mono members (rest.map (member members)) _ _ (fun joint data => ?_) later
      refine ⟨⟨data.1,?_⟩,?_⟩
      · intro other outside
        have different : other ≠ index := fun equal => outside (List.mem_cons.mpr (Or.inl equal))
        have missing : other ∉ rest := fun inside => outside (List.mem_cons_of_mem _ inside)
        simpa only [Function.update_of_ne different] using data.2 other missing
      · intro term inside
        have atUse : joint (NativePacketStep.useObject s (NativePacketRounds.useTag index)) =
            wanted (NativePacketStep.useObject s (NativePacketRounds.useTag index)) := by
          simpa only [Function.update_self] using data.2 index parts.1
        change ContextPackets.apply S joint (ContextPackets.apply S (TaggedAssignments.identity S) term) =
          ContextPackets.apply S wanted term
        rw [show ContextPackets.apply S (TaggedAssignments.identity S) term = term from
          (ContextPackets.action S (NativePacketStep.Rigid S O Γ sort)).apply_identity term]
        apply NativePacketStep.apply_at joint wanted _ atUse term
        rcases List.mem_append.mp inside with rawTerm | scopedTerm
        · exact rule_terms_location members index term rawTerm
        · rw [canonical_scope] at scopedTerm
          exact scope_terms_location members[index] (NativePacketRounds.useTag index) term scopedTerm

theorem bag_freshOn {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :
    FreshOn (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
      (scopedQueries members).scope (NativePacketRounds.source members)
      (RuleSyntax.JointFirings.bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (memberList members)) := by
  intro target incoming
  cases target
  have all := realized_indices members incoming (List.finRange members.length) (List.nodup_finRange _)
    (fun _ => TaggedAssignments.identity S)
  refine realizedOn_mono members (memberList members) _ _ (fun joint data term mentioned => ?_) all
  change ContextPackets.apply S joint (ContextPackets.apply S (TaggedAssignments.identity S) term) =
    ContextPackets.apply S incoming term
  rw [show ContextPackets.apply S (TaggedAssignments.identity S) term = term from
    (ContextPackets.action S (NativePacketStep.Rigid S O Γ sort)).apply_identity term]
  exact NativePacketStep.apply_at joint incoming _ data.1 term
    (PacketJointFreshness.source_location members term mentioned)

theorem bag_fresh {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :
    (RuleSyntax.JointFirings.bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (memberList members)).Fresh
      (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
      (NativePacketRounds.source members) := by
  intro target incoming
  cases target
  exact realizedOn_forget members (memberList members) _ (bag_freshOn members PUnit.unit incoming)

theorem scoped_admits_iff_observed {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :
    (scopedStep (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
      (scopedQueries members)).Admits (s := NativePacketRounds.source members)
        (RuleSyntax.JointFirings.bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (memberList members)) ↔
      (observedOwnStep (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
        ((scopedQueries members).profile
          (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))))).Admits
          (s := NativePacketRounds.source members)
          (RuleSyntax.JointFirings.bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (memberList members)) :=
  ⟨And.left,fun admitted => ⟨admitted,bag_freshOn members⟩⟩

theorem scoped_admits_iff_queries {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :
    (scopedStep (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
      (scopedQueries members)).Admits (s := NativePacketRounds.source members)
        (RuleSyntax.JointFirings.bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (memberList members)) ↔
      (memberList members) ≠ [] ∧
        (RuleSyntax.JointFirings.bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (memberList members)).AdmitsOwn
          (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
          (NativePacketRounds.source members) ∧
        ∀ index : Fin members.length,
          ∀ query ∈ NativePacketGuardedAdmission.questions members[index] (NativePacketRounds.useTag index),
            query.Ask (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
              (NativePacketQueryCuts.memberProblem members index) (NativePacketRounds.label members) (NativePacketStep.present s) := by
  rw [scoped_admits_iff_observed,observedOwnStep_admits_iff,asksOwn_iff]

section Native

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

theorem scoped_native_member {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (index : Fin members.length) (shapes : native.Shapes members[index].toNative)
    (admitted : (scopedStep
      (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
      (scopedQueries members)).Admits (s := NativePacketRounds.source members)
        (RuleSyntax.JointFirings.bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (memberList members))) :
    members[index].toNative.Realized := by
  have fields := (scoped_admits_iff_queries members).mp admitted
  have listed : member members index ∈ memberList members :=
    List.mem_map.mpr ⟨index,List.mem_finRange index,rfl⟩
  have one := RuleSyntax.JointFirings.Bag.admits_member
    (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
    (fun _ _ => ⟨TaggedAssignments.identity S⟩) fields.2.1 listed
  have packetEnabled : MeTTaCalculus.OccurrenceCommits.Enabled
      (fun _ : Ports O => ()) (NativePacketStep.present s)
      ((NativePacketStep.selection members[index]).commit (T := Unit)) := one.2.1
  have enabled := (NativePacketStep.selection_enabled members[index]).mp packetEnabled
  have ordinary : ∀ check ∈ (NativePacketGuardedAdmission.body members[index] (NativePacketRounds.useTag index)).checks,
      (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Entails (NativePacketQueryCuts.memberProblem members index)
        (fun substitution => check.Holds (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) substitution
          (NativePacketRounds.label members) (NativePacketStep.present s)) := by
    intro check inside substitution model
    have point := one.2.2.2 PUnit.unit substitution (by rw [member_information]; exact model)
    have atCheck := point.1 check (by rw [member_opened]; exact inside)
    rw [member_row] at atCheck
    exact (RuleSyntax.OneFrame.checkHolds_iff (label := NativePacketRounds.label members)
      (NativePacketStep.present s) check).mp atCheck
  have nativeAsks := (NativePacketGuardedAdmission.native_asks_iff members[index]).mpr
    ((NativePacketGuardedAdmission.asks_iff members index enabled).mp ⟨ordinary,fields.2.2 index⟩)
  apply (native_admits_iff members[index].toNative).mpr
  refine ⟨shapes,enabled,?_,nativeAsks⟩
  obtain ⟨target,substitution,model⟩ := one.2.2.1
  rw [member_information] at model
  have nativeModel := ((NativePacketQueryCuts.member_models_iff members index enabled substitution).mp model).1
  exact ⟨(substitution (NativePacketStep.useObject s (NativePacketRounds.useTag index))).1.2,
    (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag index))).2,nativeModel⟩

end Native

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketScopedQueries
