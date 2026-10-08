import Mettapedia.Machines.RationalTermGraph
import Mathlib.Data.Fintype.Sum

/-!
# One-sided matching of rational term graphs

A substitution redirects selected pattern nodes into an unchanged subject
graph. Shared pattern variables use one selected target; repeated occurrences
are checked by unfolding equality, never by unifying subject nodes. A checked
finite matching certificate is equivalent to instantiation followed by the
existing graph bisimilarity. Cycles and repeated edges are retained.

This is the graph-level matching contract. Choosing rigid variable identities,
elaborating object binders and realizing a certificate in native storage are
separate boundaries. The finite certificate checker does not certify the C
allocator or assert a cost bound for enumerating all possible certificates.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RationalTermGraph.Matching

universe u v w x

variable {A : Type u} {B : Type v} {Label : Type w}

/-- Pattern nodes are rebuilt over the disjoint union. An assigned node reads
the selected subject node; subject children always stay on the subject side. -/
def instantiate (pattern : Graph A Label) (subject : Graph B Label)
    (replacement : A → Option B) : Graph (A ⊕ B) Label where
  label
    | .inl a => match replacement a with
      | none => pattern.label a
      | some b => subject.label b
    | .inr b => subject.label b
  children
    | .inl a => match replacement a with
      | none => (pattern.children a).map Sum.inl
      | some b => (subject.children b).map Sum.inr
    | .inr b => (subject.children b).map Sum.inr

/-- Independent local obligations for a one-sided graph match. -/
def IsMatching (pattern : Graph A Label) (subject : Graph B Label)
    (replacement : A → Option B) (relation : A → B → Prop) : Prop :=
  ∀ ⦃a b⦄, relation a b →
    match replacement a with
    | some target => Bisimilar subject subject target b
    | none => pattern.label a = subject.label b ∧
        List.Forall₂ relation (pattern.children a) (subject.children b)

def Matches (pattern : Graph A Label) (subject : Graph B Label)
    (replacement : A → Option B) (a : A) (b : B) : Prop :=
  ∃ relation, IsMatching pattern subject replacement relation ∧ relation a b

/-- The embedding preserves subject labels, sharing and every child position
for every replacement, even one that changes the pattern arbitrarily. -/
theorem subject_transport (pattern : Graph A Label) (subject : Graph B Label)
    (replacement : A → Option B) :
    IsTransport subject (instantiate pattern subject replacement) Sum.inr := by
  constructor <;> intro b <;> rfl

theorem subject_unchanged (pattern : Graph A Label) (subject : Graph B Label)
    (replacement : A → Option B) (b : B) (depth : Nat) :
    observe (instantiate pattern subject replacement) depth (.inr b) =
      observe subject depth b := by
  exact (bisimilar_iff_observe_eq.mp
    ((subject_transport pattern subject replacement).bisimilar b) depth).symm

theorem IsMatching.instantiation_sound {pattern : Graph A Label} {subject : Graph B Label}
    {replacement : A → Option B} {relation : A → B → Prop}
    (matched : IsMatching pattern subject replacement relation) {a : A} {b : B}
    (member : relation a b) :
    Bisimilar (instantiate pattern subject replacement) subject (.inl a) b := by
  let lifted : (A ⊕ B) → B → Prop := fun node target =>
    match node with
    | .inl source => relation source target
    | .inr source => Bisimilar subject subject source target
  refine ⟨lifted, ?_, member⟩
  intro node target related
  cases node with
  | inl source =>
    have localMatch := matched related
    cases assigned : replacement source with
    | none =>
      simp only [assigned] at localMatch
      simpa only [instantiate, assigned, List.forall₂_map_left_iff] using localMatch
    | some value =>
      simp only [assigned] at localMatch
      have layer := localMatch.layer
      simpa only [instantiate, assigned, List.forall₂_map_left_iff] using layer
  | inr source =>
    have layer := related.layer
    simpa only [instantiate, List.forall₂_map_left_iff] using layer

/-- The local matching relation is also complete for the instantiated graph
observation. It does not need to identify distinct subject nodes or mutate them. -/
theorem instantiation_complete (pattern : Graph A Label) (subject : Graph B Label)
    (replacement : A → Option B) :
    IsMatching pattern subject replacement
      (fun a b => Bisimilar (instantiate pattern subject replacement) subject (.inl a) b) := by
  intro a b related
  have layer := related.layer
  cases assigned : replacement a with
  | none =>
    simpa only [instantiate, assigned, List.forall₂_map_left_iff] using layer
  | some value =>
    apply bisimilar_iff_observe_eq.mpr
    intro depth
    cases depth with
    | zero => rfl
    | succ depth =>
      have observed := bisimilar_iff_observe_eq.mp related (depth + 1)
      have expand : observe (instantiate pattern subject replacement) (depth + 1) (.inl a) =
          .node (subject.label value) ((subject.children value).map
            (fun child => observe (instantiate pattern subject replacement) depth (.inr child))) := by
        simp only [observe, instantiate, assigned, List.map_map, Function.comp_def]
      rw [expand] at observed
      simpa only [subject_unchanged, observe] using observed

theorem matches_iff_instantiation (pattern : Graph A Label) (subject : Graph B Label)
    (replacement : A → Option B) (a : A) (b : B) :
    Matches pattern subject replacement a b ↔
      Bisimilar (instantiate pattern subject replacement) subject (.inl a) b := by
  constructor
  · rintro ⟨relation, matched, member⟩
    exact matched.instantiation_sound member
  · intro related
    exact ⟨_, instantiation_complete pattern subject replacement, related⟩

section Certificates

variable [DecidableEq A] [DecidableEq B] [DecidableEq Label]

/-- A witness for each repeated capture is checked as a bisimulation, not
trusted merely because its target pair has been visited. -/
def check (pattern : Graph A Label) (subject : Graph B Label)
    (replacement : A → Option B) (pairs : List (A × B))
    (equalities : List (B × B)) (a : A) (b : B) : Bool :=
  decide ((a, b) ∈ pairs) && pairs.all (fun pair =>
    match replacement pair.1 with
    | some target => checkCertificate subject subject equalities target pair.2
    | none => decide (pattern.label pair.1 = subject.label pair.2) &&
        checkChildren pairs (pattern.children pair.1) (subject.children pair.2))

theorem check_sound {pattern : Graph A Label} {subject : Graph B Label}
    {replacement : A → Option B} {pairs : List (A × B)}
    {equalities : List (B × B)} {a : A} {b : B}
    (accepted : check pattern subject replacement pairs equalities a b = true) :
    Bisimilar (instantiate pattern subject replacement) subject (.inl a) b := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at accepted
  apply IsMatching.instantiation_sound (relation := fun a b => (a, b) ∈ pairs) ?_ accepted.1
  intro source target member
  have checked := accepted.2 (source, target) member
  cases assigned : replacement source with
  | none =>
    simpa only [assigned, Bool.and_eq_true, decide_eq_true_eq,
      checkChildren_eq_true_iff] using checked
  | some value =>
    simp only [assigned] at checked ⊢
    exact checkCertificate_sound checked

/-- On finite presentations, every match has a checked certificate. The
existence construction enumerates the witnessing relations; it does not
assert an efficient native certificate-generation algorithm. -/
theorem exists_certificate_iff_matches [Fintype A] [Fintype B]
    (pattern : Graph A Label) (subject : Graph B Label)
    (replacement : A → Option B) (a : A) (b : B) :
    (∃ pairs equalities, check pattern subject replacement pairs equalities a b = true) ↔
      Matches pattern subject replacement a b := by
  constructor
  · rintro ⟨pairs, equalities, accepted⟩
    exact (matches_iff_instantiation pattern subject replacement a b).mpr
      (check_sound accepted)
  · rintro ⟨relation, matched, member⟩
    classical
    let pairs := (Finset.univ.filter (fun pair : A × B => relation pair.1 pair.2)).toList
    let equalities := (Finset.univ.filter
      (fun pair : B × B => Bisimilar subject subject pair.1 pair.2)).toList
    have pair_mem (source : A) (target : B) :
        (source, target) ∈ pairs ↔ relation source target := by
      simp [pairs]
    have equality_mem (first second : B) :
        (first, second) ∈ equalities ↔ Bisimilar subject subject first second := by
      simp [equalities]
    have equality_checked {first second : B} (related : Bisimilar subject subject first second) :
        checkCertificate subject subject equalities first second = true := by
      apply (checkCertificate_eq_true_iff subject subject equalities first second).mpr
      refine ⟨(equality_mem first second).mpr related, ?_⟩
      intro left right member
      obtain ⟨labels, children⟩ := ((equality_mem left right).mp member).layer
      exact ⟨labels, children.imp fun x y pair => (equality_mem x y).mpr pair⟩
    refine ⟨pairs, equalities, ?_⟩
    simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨(pair_mem a b).mpr member, ?_⟩
    intro pair member
    have obligation := matched ((pair_mem pair.1 pair.2).mp member)
    cases assigned : replacement pair.1 with
    | none =>
      simp only [assigned] at obligation
      simp only [Bool.and_eq_true, decide_eq_true_eq, checkChildren_eq_true_iff]
      exact ⟨obligation.1,
        obligation.2.imp fun x y related => (pair_mem x y).mpr related⟩
    | some value =>
      simp only [assigned] at obligation ⊢
      exact equality_checked obligation

theorem exists_certificate_iff_instantiation [Fintype A] [Fintype B]
    (pattern : Graph A Label) (subject : Graph B Label)
    (replacement : A → Option B) (a : A) (b : B) :
    (∃ pairs equalities, check pattern subject replacement pairs equalities a b = true) ↔
      Bisimilar (instantiate pattern subject replacement) subject (.inl a) b :=
  (exists_certificate_iff_matches pattern subject replacement a b).trans
    (matches_iff_instantiation pattern subject replacement a b)

end Certificates

section RigidIdentities

variable {Variable : Type x} [DecidableEq Variable]

/-- The subject inventory and pattern hole identities choose the replacement
domain. A spelling is not used as a substitute for a variable identity. -/
def captures (hole : A → Option Variable) (rigid : Finset Variable)
    (bindings : Variable → Option B) (a : A) : Option B :=
  match hole a with
  | none => none
  | some key => if key ∈ rigid then none else bindings key

theorem captures_excludes_subject {hole : A → Option Variable} {rigid : Finset Variable}
    {bindings : Variable → Option B} {a : A} {key : Variable}
    (atHole : hole a = some key) (subjectVariable : key ∈ rigid) :
    captures hole rigid bindings a = none := by
  simp [captures, atHole, subjectVariable]

theorem repeated_hole_has_one_target (hole : A → Option Variable) (rigid : Finset Variable)
    (bindings : Variable → Option B) {a a' : A} (same : hole a = hole a') :
    captures hole rigid bindings a = captures hole rigid bindings a' := by
  simp only [captures, same]

end RigidIdentities

end Mettapedia.Machines.RationalTermGraph.Matching
