import Mettapedia.GSLT.LanguageDef.NIKGSLT
import Mettapedia.Languages.TPTP.StatusSemantics

/-!
# Fail-closed chronological authority for TPTP derivations

A TSTP derivation is a chronological DAG whose internal nodes name an
inference rule, an SZS semantic status, parent nodes, and an inferred formula.
The rule name is open vocabulary; authority therefore comes from an indexed
family of admitted rule checkers rather than a closed case split in NIK.

This module proves exact certificate completeness for the declared certified
scope of every local rule and a sound projection to independently stated
guest semantics.  Leaves remain an explicit initial environment: matching
them against a parsed TPTP problem is a separate authority that composes at
the NIK boundary.
-/

namespace Mettapedia.Languages.TPTP.NIKAuthority

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.NIKGSLT
open Mettapedia.Languages.TPTP.StatusSemantics

universe uFormula uCertificate

/-! ## Open rule registry -/

/-- A rule authority is indexed by both its open rule name and its claimed
semantic status. -/
structure RuleKey where
  rule : String
  status : Status
deriving DecidableEq, Repr

/-- Independently admitted rule checkers for one formula language. -/
structure RuleAuthorityFamily (Formula : Type uFormula)
    (semantics : StatusMeaning Formula) where
  Certificate : RuleKey -> Type uCertificate
  checker : (key : RuleKey) -> Checker (RelationClaim Formula) (Certificate key)
  Certified : RuleKey -> RelationClaim Formula -> Prop
  projection : (key : RuleKey) ->
    (checker key).AuthorityProjection (Certified key)
      (semantics.Meaning key.status)

namespace RuleAuthorityFamily

variable {Formula : Type uFormula} {semantics : StatusMeaning Formula}
    (family : RuleAuthorityFamily Formula semantics)

/-- The generic dependent authority-family view used by NIK dispatch. -/
def toAuthorityFamily : AuthorityFamily RuleKey where
  Claim := fun _ => RelationClaim Formula
  Certificate := family.Certificate
  checker := family.checker
  Certified := family.Certified
  Meaning := fun key => semantics.Meaning key.status
  projection := family.projection

abbrev PackedCertificate := family.toAuthorityFamily.PackedCertificate

end RuleAuthorityFamily

/-! ## Chronological skeleton and semantic replay -/

structure Entry (Formula : Type uFormula) where
  id : Nat
  formula : Formula
deriving Repr

structure Node (Formula : Type uFormula) where
  id : Nat
  key : RuleKey
  parentIds : List Nat
  inferred : Formula
deriving Repr

/-- Evidence-free proof shape.  Rule certificates are transported separately
so certificate completeness can quantify over them honestly. -/
structure Skeleton (Formula : Type uFormula) where
  initial : List (Entry Formula)
  nodes : List (Node Formula)
  rootId : Nat
  expected : Formula
deriving Repr

def findEntry? {Formula : Type uFormula} :
    List (Entry Formula) -> Nat -> Option (Entry Formula)
  | [], _ => none
  | entry :: entries, id =>
      if entry.id = id then some entry else findEntry? entries id

def resolveParents? {Formula : Type uFormula}
    (entries : List (Entry Formula)) : List Nat -> Option (List Formula)
  | [] => some []
  | id :: ids => do
      let entry ← findEntry? entries id
      let formulas ← resolveParents? entries ids
      some (entry.formula :: formulas)

def nodeClaim {Formula : Type uFormula} (node : Node Formula)
    (parents : List Formula) : RelationClaim Formula :=
  { parents := parents
    inferred := node.inferred }

/-- Independent semantic replay of a chronological skeleton.  The predicate
`Property` is either the exact local certificate scope or the projected guest
meaning. -/
inductive Replay {Formula : Type uFormula}
    (Property : RuleKey -> RelationClaim Formula -> Prop) :
    List (Entry Formula) -> List (Node Formula) -> List (Entry Formula) -> Prop
  | nil (entries) : Replay Property entries [] entries
  | cons {entries parents nodes final} (node : Node Formula) :
      findEntry? entries node.id = none ->
      resolveParents? entries node.parentIds = some parents ->
      Property node.key (nodeClaim node parents) ->
      Replay Property ({ id := node.id, formula := node.inferred } :: entries)
        nodes final ->
      Replay Property entries (node :: nodes) final

def RootMatches {Formula : Type uFormula} (entries : List (Entry Formula))
    (rootId : Nat) (expected : Formula) : Prop :=
  exists entry, findEntry? entries rootId = some entry /\
    entry.formula = expected

def ProofProperty {Formula : Type uFormula}
    (Property : RuleKey -> RelationClaim Formula -> Prop)
    (skeleton : Skeleton Formula) : Prop :=
  (skeleton.initial.map Entry.id).Nodup /\
    exists final,
      Replay Property skeleton.initial skeleton.nodes final /\
        RootMatches final skeleton.rootId skeleton.expected

/-! ## Executable replay -/

def checkNodes? {Formula : Type uFormula}
    {semantics : StatusMeaning Formula}
    (family : RuleAuthorityFamily Formula semantics) [DecidableEq RuleKey] :
    List (Entry Formula) -> List (Node Formula) ->
      List family.PackedCertificate -> Option (List (Entry Formula))
  | entries, [], [] => some entries
  | entries, node :: nodes, certificate :: certificates => do
      if (findEntry? entries node.id).isSome then none else
        let parents ← resolveParents? entries node.parentIds
        let claim : family.toAuthorityFamily.PackedClaim :=
          ⟨node.key, nodeClaim node parents⟩
        if family.toAuthorityFamily.packedChecker.check claim certificate then
          checkNodes? family
            ({ id := node.id, formula := node.inferred } :: entries)
            nodes certificates
        else
          none
  | _, _, _ => none

def rootMatchesB {Formula : Type uFormula} [DecidableEq Formula]
    (entries : List (Entry Formula)) (rootId : Nat) (expected : Formula) : Bool :=
  match findEntry? entries rootId with
  | none => false
  | some entry => decide (entry.formula = expected)

def checkProof {Formula : Type uFormula} [DecidableEq Formula]
    {semantics : StatusMeaning Formula}
    (family : RuleAuthorityFamily Formula semantics)
    (skeleton : Skeleton Formula)
    (certificates : List family.PackedCertificate) : Bool :=
  decide (skeleton.initial.map Entry.id).Nodup &&
    match checkNodes? family skeleton.initial skeleton.nodes certificates with
    | none => false
    | some final => rootMatchesB final skeleton.rootId skeleton.expected

/-! ## Exactness of chronological replay -/

private theorem findEntry?_isSome_false_iff
    {Formula : Type uFormula} {entries : List (Entry Formula)} {id : Nat} :
    (findEntry? entries id).isSome = false <-> findEntry? entries id = none := by
  cases findEntry? entries id <;> simp

theorem checkNodes?_sound
    {Formula : Type uFormula} {semantics : StatusMeaning Formula}
    (family : RuleAuthorityFamily Formula semantics) [DecidableEq RuleKey]
    {entries : List (Entry Formula)} {nodes : List (Node Formula)}
    {certificates : List family.PackedCertificate}
    {final : List (Entry Formula)}
    (checked : checkNodes? family entries nodes certificates = some final) :
    Replay family.Certified entries nodes final := by
  induction nodes generalizing entries certificates with
  | nil =>
      cases certificates with
      | nil =>
          simp [checkNodes?] at checked
          subst final
          exact .nil entries
      | cons certificate certificates => simp [checkNodes?] at checked
  | cons node nodes inductionHypothesis =>
      cases certificates with
      | nil => simp [checkNodes?] at checked
      | cons certificate certificates =>
          simp only [checkNodes?] at checked
          have fresh : (findEntry? entries node.id).isSome = false := by
            split at checked
            next duplicate => simp at checked
            next notDuplicate =>
              exact Bool.eq_false_of_not_eq_true notDuplicate
          simp only [fresh, Bool.false_eq_true, ↓reduceIte] at checked
          cases resolved : resolveParents? entries node.parentIds with
          | none => simp [resolved] at checked
          | some parents =>
              simp [resolved] at checked
              let claim : family.toAuthorityFamily.PackedClaim :=
                ⟨node.key, nodeClaim node parents⟩
              obtain ⟨accepted, checkedRest⟩ := checked
              have certifiedPacked :=
                family.toAuthorityFamily.packedChecker_sound
                  claim certificate accepted
              have certified :
                  family.Certified node.key (nodeClaim node parents) :=
                certifiedPacked
              exact Replay.cons node
                (findEntry?_isSome_false_iff.mp fresh) resolved certified
                (inductionHypothesis checkedRest)

theorem checkNodes?_complete
    {Formula : Type uFormula} {semantics : StatusMeaning Formula}
    (family : RuleAuthorityFamily Formula semantics) [DecidableEq RuleKey]
    {entries : List (Entry Formula)} {nodes : List (Node Formula)}
    {final : List (Entry Formula)}
    (replay : Replay family.Certified entries nodes final) :
    exists certificates : List family.PackedCertificate,
      checkNodes? family entries nodes certificates = some final := by
  induction replay with
  | nil entries => exact ⟨[], rfl⟩
  | @cons entries parents nodes final node fresh resolved certified rest ih =>
      obtain ⟨certificate, accepted⟩ :=
        (family.projection node.key).authority.complete
          (nodeClaim node parents) certified
      obtain ⟨certificates, checkedRest⟩ := ih
      let packed : family.PackedCertificate := ⟨node.key, certificate⟩
      refine ⟨packed :: certificates, ?_⟩
      simp only [checkNodes?]
      have notSome : (findEntry? entries node.id).isSome = false := by
        exact findEntry?_isSome_false_iff.mpr fresh
      simp only [notSome, Bool.false_eq_true, ↓reduceIte, resolved]
      have packedAccepted :
          family.toAuthorityFamily.packedChecker.check
            ⟨node.key, nodeClaim node parents⟩ packed = true := by
        simpa [packed, RuleAuthorityFamily.toAuthorityFamily] using accepted
      simp [packedAccepted, checkedRest]

theorem rootMatchesB_eq_true_iff
    {Formula : Type uFormula} [DecidableEq Formula]
    (entries : List (Entry Formula)) (rootId : Nat) (expected : Formula) :
    rootMatchesB entries rootId expected = true <->
      RootMatches entries rootId expected := by
  unfold rootMatchesB RootMatches
  cases found : findEntry? entries rootId with
  | none => simp
  | some entry => simp

def proofChecker {Formula : Type uFormula} [DecidableEq Formula]
    {semantics : StatusMeaning Formula}
    (family : RuleAuthorityFamily Formula semantics) :
    Checker (Skeleton Formula) (List family.PackedCertificate) where
  check := checkProof family

def Certified {Formula : Type uFormula}
    {semantics : StatusMeaning Formula}
    (family : RuleAuthorityFamily Formula semantics) : Skeleton Formula -> Prop :=
  ProofProperty family.Certified

def Meaning {Formula : Type uFormula}
    {semantics : StatusMeaning Formula}
    (_family : RuleAuthorityFamily Formula semantics) : Skeleton Formula -> Prop :=
  ProofProperty (fun key => semantics.Meaning key.status)

theorem proofChecker_sound
    {Formula : Type uFormula} [DecidableEq Formula]
    {semantics : StatusMeaning Formula}
    (family : RuleAuthorityFamily Formula semantics) :
    (proofChecker family).Sound (Certified family) := by
  intro skeleton certificates accepted
  have parts :
      decide (skeleton.initial.map Entry.id).Nodup = true /\
        (match checkNodes? family skeleton.initial skeleton.nodes certificates with
         | none => false
         | some final =>
             rootMatchesB final skeleton.rootId skeleton.expected) = true := by
    simpa only [proofChecker, checkProof, Bool.and_eq_true] using accepted
  have initialUnique : (skeleton.initial.map Entry.id).Nodup :=
    of_decide_eq_true parts.1
  cases checked : checkNodes? family skeleton.initial skeleton.nodes certificates with
  | none => simp [checked] at parts
  | some final =>
      refine ⟨initialUnique, final, checkNodes?_sound family checked, ?_⟩
      exact (rootMatchesB_eq_true_iff final skeleton.rootId skeleton.expected).mp
        (by simpa [checked] using parts.2)

theorem proofChecker_complete
    {Formula : Type uFormula} [DecidableEq Formula]
    {semantics : StatusMeaning Formula}
    (family : RuleAuthorityFamily Formula semantics) :
    (proofChecker family).CertificateComplete (Certified family) := by
  intro skeleton certified
  obtain ⟨initialUnique, final, replay, root⟩ := certified
  obtain ⟨certificates, checked⟩ := checkNodes?_complete family replay
  refine ⟨certificates, ?_⟩
  simp only [proofChecker, checkProof, Bool.and_eq_true]
  constructor
  · exact decide_eq_true initialUnique
  · simp only [checked]
    exact (rootMatchesB_eq_true_iff final skeleton.rootId skeleton.expected).mpr root

theorem proofChecker_authority
    {Formula : Type uFormula} [DecidableEq Formula]
    {semantics : StatusMeaning Formula}
    (family : RuleAuthorityFamily Formula semantics) :
    (proofChecker family).Authority (Certified family) where
  sound := proofChecker_sound family
  complete := proofChecker_complete family

theorem Replay.map
    {Formula : Type uFormula}
    {Strong Weak : RuleKey -> RelationClaim Formula -> Prop}
    (project : forall key claim, Strong key claim -> Weak key claim)
    {entries nodes final} (replay : Replay Strong entries nodes final) :
    Replay Weak entries nodes final := by
  induction replay with
  | nil entries => exact .nil entries
  | cons node fresh resolved strong rest ih =>
      exact .cons node fresh resolved (project node.key _ strong) ih

theorem certified_implies_meaning
    {Formula : Type uFormula} {semantics : StatusMeaning Formula}
    (family : RuleAuthorityFamily Formula semantics)
    (skeleton : Skeleton Formula) :
    Certified family skeleton -> Meaning family skeleton := by
  rintro ⟨unique, final, replay, root⟩
  refine ⟨unique, final, replay.map ?_, root⟩
  intro key claim certified
  exact (family.projection key).project claim certified

/-- The chronological checker is exact for its declared per-rule certificate
scope and sound for the guest logic's independently stated status meanings. -/
def proofChecker_authorityProjection
    {Formula : Type uFormula} [DecidableEq Formula]
    {semantics : StatusMeaning Formula}
    (family : RuleAuthorityFamily Formula semantics) :
    (proofChecker family).AuthorityProjection (Certified family) (Meaning family) where
  authority := proofChecker_authority family
  project := certified_implies_meaning family

/-! ## NIK reification -/

def theory {Formula : Type uFormula} [DecidableEq Formula]
    {semantics : StatusMeaning Formula}
    (family : RuleAuthorityFamily Formula semantics) :=
  Atomic.theory (proofChecker family)

theorem acceptance_implies_meaning
    {Formula : Type uFormula} [DecidableEq Formula]
    {semantics : StatusMeaning Formula}
    (family : RuleAuthorityFamily Formula semantics)
    {skeleton : Skeleton Formula}
    {certificates : List family.PackedCertificate}
    (path : (theory family).MultiStep
      (.submitted skeleton certificates) (.accepted skeleton)) :
    Meaning family skeleton := by
  exact Refinement.acceptance_sound (Refinement.atomic (proofChecker family))
    (proofChecker_authorityProjection family).sound path

/-! ## Finite semantic canaries -/

namespace Canary

open StatusSemantics.Canary

/-- Finite decision procedure for the independently defined Boolean-model
meaning. -/
def boolStatusPredicate (status : Status) (claim : RelationClaim Bool) : Prop :=
  match status with
  | .thm => claim.parents.all id = true -> claim.inferred = true
  | .cth => claim.parents.all id = true -> claim.inferred = false
  | .esa => claim.parents.all id = true <-> claim.inferred = true
  | _ => False

/-- Executable decision of the finite Boolean-model instance. -/
def boolStatusCheck (status : Status) (claim : RelationClaim Bool) : Bool :=
  match status with
  | .thm => !(claim.parents.all id) || claim.inferred
  | .cth => !(claim.parents.all id) || !claim.inferred
  | .esa => claim.parents.all id == claim.inferred
  | _ => false

theorem boolStatusCheck_eq_true_iff_predicate
    (status : Status) (claim : RelationClaim Bool) :
    boolStatusCheck status claim = true <->
      boolStatusPredicate status claim := by
  cases status <;>
    simp only [boolStatusCheck, boolStatusPredicate, Bool.false_eq_true] <;>
    try {
      cases parentsTrue : claim.parents.all id <;>
      cases inferred : claim.inferred <;>
      simp }

@[simp] theorem boolSatisfiesAll_iff_all_true (model : Unit)
    (formulas : List Bool) :
    boolSemantics.SatisfiesAll model formulas <-> formulas.all id = true := by
  cases model
  simp [ClassicalModelSemantics.SatisfiesAll, boolSemantics,
    List.all_eq_true]

theorem boolSatisfiable_iff_all_true (formulas : List Bool) :
    boolSemantics.Satisfiable formulas <-> formulas.all id = true := by
  constructor
  · rintro ⟨model, satisfied⟩
    exact (boolSatisfiesAll_iff_all_true model formulas).mp satisfied
  · intro allTrue
    exact ⟨(), (boolSatisfiesAll_iff_all_true () formulas).mpr allTrue⟩

theorem boolStatusPredicate_iff_meaning
    (status : Status) (claim : RelationClaim Bool) :
    boolStatusPredicate status claim <->
      boolSemantics.commonStatusMeaning.Meaning status claim := by
  cases status <;>
    simp [boolStatusPredicate,
      ClassicalModelSemantics.commonStatusMeaning,
      ClassicalModelSemantics.TheoremRelation,
      ClassicalModelSemantics.CounterTheoremRelation,
      ClassicalModelSemantics.EquiSatisfiableRelation,
      boolSatisfiesAll_iff_all_true, boolSatisfiable_iff_all_true,
      boolSemantics.satisfies_negate] <;>
    simp [boolSemantics]

def finiteRuleFamily :
    RuleAuthorityFamily Bool boolSemantics.commonStatusMeaning where
  Certificate := fun _ => Unit
  checker := fun key =>
    { check := fun claim _ =>
        boolStatusCheck key.status claim }
  Certified := fun key => boolSemantics.commonStatusMeaning.Meaning key.status
  projection := by
    intro key
    exact
      { authority :=
          { sound := by
              intro claim certificate accepted
              exact (boolStatusPredicate_iff_meaning key.status claim).mp
                ((boolStatusCheck_eq_true_iff_predicate key.status claim).mp
                  accepted)
            complete := by
              intro claim meaningful
              exact ⟨(),
                (boolStatusCheck_eq_true_iff_predicate key.status claim).mpr
                  ((boolStatusPredicate_iff_meaning key.status claim).mpr
                    meaningful)⟩ }
        project := by intro claim meaningful; exact meaningful }

def theoremKey : RuleKey := ⟨"resolution", .thm⟩

def validSkeleton : Skeleton Bool where
  initial := [⟨0, true⟩]
  nodes := [⟨1, theoremKey, [0], true⟩]
  rootId := 1
  expected := true

def validEvidence : List finiteRuleFamily.PackedCertificate :=
  [⟨theoremKey, ()⟩]

theorem valid_proof_accepted :
    checkProof finiteRuleFamily validSkeleton validEvidence = true := by
  decide

def wrongStatusEvidence : List finiteRuleFamily.PackedCertificate :=
  [⟨⟨"resolution", .cth⟩, ()⟩]

/-- Cross-status evidence is rejected even when its payload has the same
runtime representation. -/
theorem wrong_status_rejected :
    checkProof finiteRuleFamily validSkeleton wrongStatusEvidence = false := by
  decide

def missingParentSkeleton : Skeleton Bool :=
  { validSkeleton with
    nodes := [⟨1, theoremKey, [99], true⟩] }

theorem missing_parent_rejected :
    checkProof finiteRuleFamily missingParentSkeleton validEvidence = false := by
  decide

end Canary

end Mettapedia.Languages.TPTP.NIKAuthority
