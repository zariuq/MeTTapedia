import Mettapedia.Languages.MeTTa.HE.MatcherBridge
import Mettapedia.Languages.MeTTa.HE.SmallStep
import Mettapedia.Languages.MeTTa.HE.DeclMatchSpec
import Mettapedia.Languages.MeTTa.HE.Space
import Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.RuntimeCorrectness
import MettaHyperonFull.Minimal.Interpreter
import MettaHyperonFull.Operational.Properties
import MettaHyperonFull.Proofs.Alpha
import MettaHyperonFull.Proofs.IndexingComplete
import MettaHyperonFull.Proofs.Preservation
import MettaHyperonFull.Proofs.Substitution

/-!
# HE <-> LeaTTa Bridge Basics

This file starts the Lean-side bridge between Mettapedia's HE atom/space
surface and LeaTTa's verified Meta-MeTTa core. The first step is deliberately
small and honest: a structural translation on atoms plus the shape-preservation
lemmas that later simulation proofs will need.

What is proved here:

* `toLeaTTaAtom` / `toLeaTTaSpace` - structural translation
* head-key preservation on the symbol-headed fragment
* equation-rule extraction preservation

What is intentionally deferred:

* matching/unification correspondence
* QUERY/equation-step simulation
* grounded numeric-tower alignment
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge

/-- Translate HE grounded payloads into LeaTTa grounded payloads.

`custom` payloads are mapped into LeaTTa's `external` lane. This is a structural
embedding only; no claim is made yet that the host-side operational semantics of
custom/external payloads coincide. -/
def toLeaTTaGround : GroundedValue → Metta.Ground
  | .int n => .int n
  | .string s => .str s
  | .bool b => .bool b
  | .custom typeName payload => .external typeName payload

/-- Numeric boundary: HE grounded values never translate to LeaTTa host floats. -/
theorem toLeaTTaGround_ne_float (g : GroundedValue) (f : Float) :
    toLeaTTaGround g ≠ .float f := by
  cases g <;> simp [toLeaTTaGround]

/-- Runtime boundary: HE grounded values never translate to LeaTTa's host-side
unit payload. -/
theorem toLeaTTaGround_ne_unit (g : GroundedValue) :
    toLeaTTaGround g ≠ .unit := by
  cases g <;> simp [toLeaTTaGround]

/-- Error-contour boundary: HE grounded values never translate directly to
LeaTTa's grounded `error` payload constructor. -/
theorem toLeaTTaGround_ne_error (g : GroundedValue) (msg : String) :
    toLeaTTaGround g ≠ .error msg := by
  cases g <;> simp [toLeaTTaGround]

mutual

/-- Structural HE-atom translation into LeaTTa atoms. -/
def toLeaTTaAtom : Atom → Metta.Atom
  | .symbol s => .sym s
  | .var v => .var v
  | .grounded g => .gnd (toLeaTTaGround g)
  | .expression es => .expr (toLeaTTaAtoms es)

/-- Structural translation on atom lists. -/
def toLeaTTaAtoms : List Atom → List Metta.Atom
  | [] => []
  | a :: as => toLeaTTaAtom a :: toLeaTTaAtoms as

end

@[simp] private theorem substOccurs_symbol (v s : String) :
    Metta.Subst.occurs v (Metta.Atom.sym s) = false := by
  simp [Metta.Subst.occurs]

@[simp] private theorem substOccurs_grounded (v : String) (g : Metta.Ground) :
    Metta.Subst.occurs v (Metta.Atom.gnd g) = false := by
  simp [Metta.Subst.occurs]

private theorem toLeaTTaGround_equiv_self (g : GroundedValue) :
    Metta.Ground.equiv (toLeaTTaGround g) (toLeaTTaGround g) = true := by
  cases g with
  | int n =>
      change (Metta.Ground.int n == Metta.Ground.int n) = true
      change (n == n) = true
      exact beq_self_eq_true n
  | string s =>
      change (Metta.Ground.str s == Metta.Ground.str s) = true
      change (s == s) = true
      exact beq_self_eq_true s
  | bool b =>
      change (Metta.Ground.bool b == Metta.Ground.bool b) = true
      change (b == b) = true
      exact beq_self_eq_true b
  | custom typeName payload =>
      change (Metta.Ground.external typeName payload ==
        Metta.Ground.external typeName payload) = true
      change ((typeName == typeName) && (payload == payload)) = true
      simp

theorem toLeaTTaAtom_grounded_equiv_self (g : GroundedValue) :
    Metta.Atom.equiv (toLeaTTaAtom (.grounded g)) (toLeaTTaAtom (.grounded g)) = true := by
  simpa [toLeaTTaAtom, Metta.Atom.equiv] using toLeaTTaGround_equiv_self g

/-- Translate an HE space into a LeaTTa space by translating its atom list. -/
def toLeaTTaSpace (space : Space) : Metta.Space :=
  ⟨toLeaTTaAtoms space.atoms⟩

/-- HE-side analogue of LeaTTa's `headKey`, used to state shape preservation
without prematurely committing to the whole step relation. -/
def heHeadKey : Atom → Option String
  | .symbol s => some s
  | .expression (.symbol s :: _) => some s
  | _ => none

/-- Canonical LeaTTa substitution induced by an HE assignment list.

Assignments are processed right-to-left so that the leftmost HE lookup wins,
matching `List.lookup` on the original assignment list. -/
def toLeaTTaSubst : List (String × Atom) → Metta.Subst
  | [] => []
  | (v, a) :: rest => Metta.Subst.extend (toLeaTTaSubst rest) v (toLeaTTaAtom a)

/-- Matcher-oriented LeaTTa substitution induced by an HE assignment list.

HE's `simpleMatch` appends fresh assignments as variables are first discovered,
while LeaTTa's matcher-facing bindings grow by prepending fresh `val` relations.
Reversing the HE assignment list aligns the two concrete binding orders. -/
def toLeaTTaMatchSubst (assigns : List (String × Atom)) : Metta.Subst :=
  assigns.reverse.map fun (v, a) => (v, toLeaTTaAtom a)

/-- Assignment-only LeaTTa bindings induced by the HE assignment surface. -/
def toLeaTTaAssignmentBindings (b : Bindings) : Metta.Bindings :=
  Metta.Bindings.ofSubst (toLeaTTaSubst b.assignments)

/-- Matcher-oriented LeaTTa bindings induced by an HE assignment list. This is
the concrete binding shape that lines up with LeaTTa's `matchAtoms` output
ordering, as opposed to the substitution-oriented `toLeaTTaAssignmentBindings`.
-/
def toLeaTTaMatchBindings (b : Bindings) : Metta.Bindings :=
  Metta.Bindings.ofSubst (toLeaTTaMatchSubst b.assignments)

/-- One HE assignment as a LeaTTa relation. Bare-variable targets are aliases;
all other targets are direct values. -/
def toLeaTTaAssignmentRel : String × Atom → Metta.BindingRel
  | (v, .var w) => .eq v w
  | (v, value) => .val v (toLeaTTaAtom value)

/-- Concrete normal form of the assignment-only matcher translation. -/
theorem toLeaTTaMatchBindings_eq_map (b : Bindings) :
    toLeaTTaMatchBindings b =
      b.assignments.reverse.map toLeaTTaAssignmentRel := by
  simp only [toLeaTTaMatchBindings, toLeaTTaMatchSubst,
    Metta.Bindings.ofSubst, List.map_map]
  apply List.map_congr_left
  intro p _
  rcases p with ⟨v, value⟩
  cases value <;> rfl

/-- Explicit HE equalities in LeaTTa's matcher orientation and chronology.

HE records a query/pattern variable equality by appending `(query, pattern)`.
LeaTTa records the same match by prepending `eq pattern query`. Reversing and
swapping therefore preserves the representative order used by both resolvers. -/
def toLeaTTaEqualityBindings (b : Bindings) : Metta.Bindings :=
  b.equalities.reverse.map fun (queryVar, patternVar) =>
    .eq patternVar queryVar

/-- Canonical full translation of an HE binding set.

Equality relations precede assignment relations so a bare-variable assignment,
when one is present in an arbitrary HE seed, retains its directed target as the
LeaTTa class representative. Matcher-produced bindings use explicit HE
equalities for variable/variable constraints. -/
def toLeaTTaMatchBindingsFull (b : Bindings) : Metta.Bindings :=
  toLeaTTaEqualityBindings b ++ toLeaTTaMatchBindings b

/-- Order-free value-relation agreement between an HE record and a LeaTTa
binding set. This compares relation membership rather than concrete list order. -/
def LeaValueRelEquiv (b : Bindings) (lb : Metta.Bindings) : Prop :=
  ∀ v value,
    Metta.BindingRel.val v value ∈ lb ↔
      ∃ heValue, (v, heValue) ∈ b.assignments ∧
        value = toLeaTTaAtom heValue

/-- Order-free equality-edge agreement. Equality is symmetric in the official
binding-set semantics, so relation orientation is deliberately quotiented. -/
def LeaEqualityRelEquiv (b : Bindings) (lb : Metta.Bindings) : Prop :=
  ∀ x y,
    (Metta.BindingRel.eq x y ∈ lb ∨ Metta.BindingRel.eq y x ∈ lb) ↔
      ((x, y) ∈ b.equalities ∨ (y, x) ∈ b.equalities)

/-- Representation-independent agreement of the two binding surfaces. The
relation follows the English specification's order-free binding-set semantics:
direct values agree structurally, and explicit aliases agree as undirected
edges. Resolver and instantiation correspondence are consequences to prove,
not fields smuggled into this definition. -/
structure LeaBindingRelEquiv (b : Bindings) (lb : Metta.Bindings) : Prop where
  values : LeaValueRelEquiv b lb
  equalities : LeaEqualityRelEquiv b lb

/-- Structural variable disjointness for query/rule matching, independent of
the fuel-bounded HE variable collector. -/
def VarsDisjoint (left right : Atom) : Prop :=
  ∀ v, v ∈ (toLeaTTaAtom left).vars →
    v ∉ (toLeaTTaAtom right).vars

/-- Structural variable disjointness is symmetric. -/
theorem VarsDisjoint.symm {left right : Atom}
    (h : VarsDisjoint left right) : VarsDisjoint right left := by
  intro v hright hleft
  exact h v hleft hright

-- Structural depth measures for HE atoms and atom lists.
mutual

def atomDepth : Atom → Nat
  | .symbol _ => 0
  | .var _ => 0
  | .grounded _ => 0
  | .expression es => listDepth es + 1

def listDepth : List Atom → Nat
  | [] => 0
  | a :: as => max (atomDepth a) (listDepth as)

end

/-- Boundary predicate for the fragment where HE's recursive `resolve` agrees
with LeaTTa's one-pass substitution: no HE lookup produces a bare variable. -/
def NoVarAssignmentValues (b : Bindings) : Prop :=
  ∀ ⦃v x⦄, b.lookup v = some (.var x) → False

/-- Syntactic form of the same matcher invariant: no stored assignment has a
bare-variable value. Unlike `NoVarAssignmentValues`, this sees every list entry
and therefore needs no uniqueness premise when used directly. -/
def NoBareVarAssignments (b : Bindings) : Prop :=
  ∀ ⦃v x⦄, (v, .var x) ∉ b.assignments

/-- No variable occurring inside an assignment value has another direct
assignment in the same HE binding set. -/
def AssignmentValuesIndependent (b : Bindings) : Prop :=
  ∀ ⦃v a⦄, b.lookup v = some a → b.hasAssignedVar a = false

/-- HE assignment-key uniqueness, stated explicitly so bridge lemmas can use it
without reaching into private helper files. -/
def AssignmentsNodup (b : Bindings) : Prop :=
  (b.assignments.map Prod.fst).Nodup

@[simp] theorem toLeaTTaEqualityBindings_empty :
    toLeaTTaEqualityBindings Bindings.empty = [] := rfl

@[simp] theorem toLeaTTaMatchBindingsFull_empty :
    toLeaTTaMatchBindingsFull Bindings.empty = [] := rfl

/-- Empty bindings agree on both relation kinds. -/
@[simp] theorem LeaBindingRelEquiv.empty :
    LeaBindingRelEquiv Bindings.empty Metta.Bindings.empty := by
  constructor
  · intro v value
    simp [Bindings.empty, Metta.Bindings.empty]
  · intro x y
    simp [Bindings.empty, Metta.Bindings.empty]

/-- A single HE query/pattern equality translates to LeaTTa's opposite matcher
orientation. -/
example :
    toLeaTTaMatchBindingsFull ⟨[], [("q", "p")]⟩ =
      [Metta.BindingRel.eq "p" "q"] := by
  rfl

/-- The minimal connected-class matcher output has exactly the repaired LeaTTa
edge chronology. -/
example :
    toLeaTTaMatchBindingsFull
        ⟨[], [("q1", "p1"), ("q1", "p2"), ("q2", "p2")]⟩ =
      [Metta.BindingRel.eq "p2" "q2",
        Metta.BindingRel.eq "p2" "q1",
        Metta.BindingRel.eq "p1" "q1"] := by
  rfl

/-- POSITIVE: order-free equivalence accepts the mixed relation order emitted
by LeaTTa's prepend-based merge. -/
example :
    LeaBindingRelEquiv
      ⟨[("r", .symbol "a")], [("q", "p")]⟩
      [Metta.BindingRel.val "r" (.sym "a"),
        Metta.BindingRel.eq "p" "q"] := by
  constructor
  · intro v value
    simp [toLeaTTaAtom]
  · intro x y
    simp only [List.mem_cons, List.not_mem_nil,
      or_false, Metta.BindingRel.eq.injEq, Prod.mk.injEq]
    aesop

/-- NEGATIVE: the same semantically equivalent mixed binding is not the
canonical concrete relation list. -/
example :
    [Metta.BindingRel.val "r" (.sym "a"),
        Metta.BindingRel.eq "p" "q"] ≠
      toLeaTTaMatchBindingsFull
        ⟨[("r", .symbol "a")], [("q", "p")]⟩ := by
  simp [toLeaTTaMatchBindingsFull, toLeaTTaEqualityBindings,
    toLeaTTaMatchBindings, toLeaTTaMatchSubst, Metta.Bindings.ofSubst,
    toLeaTTaAtom]

private theorem noVarAssignmentValues_of_extends
    {seed result : Bindings}
    (hext : seed.Extends result)
    (hno : NoVarAssignmentValues result) :
    NoVarAssignmentValues seed := by
  intro v x hlookup
  exact hno (hext v (.var x) hlookup)

@[simp] theorem toLeaTTaAtoms_nil :
    toLeaTTaAtoms [] = [] := rfl

@[simp] theorem toLeaTTaAtoms_cons (a : Atom) (as : List Atom) :
    toLeaTTaAtoms (a :: as) = toLeaTTaAtom a :: toLeaTTaAtoms as := rfl

private theorem mem_toLeaTTaAtoms_of_mem {atoms : List Atom} {a : Atom}
    (h : a ∈ atoms) :
    toLeaTTaAtom a ∈ toLeaTTaAtoms atoms := by
  induction atoms with
  | nil => cases h
  | cons hd tl ih =>
      simp at h ⊢
      exact h.elim (fun h => Or.inl (congrArg toLeaTTaAtom h))
        (fun h => Or.inr (ih h))

@[simp] theorem toLeaTTaSubst_nil :
    toLeaTTaSubst [] = [] := rfl

@[simp] theorem toLeaTTaSubst_cons (v : String) (a : Atom) (rest : List (String × Atom)) :
    toLeaTTaSubst ((v, a) :: rest) =
      Metta.Subst.extend (toLeaTTaSubst rest) v (toLeaTTaAtom a) := rfl

@[simp] theorem toLeaTTaMatchSubst_nil :
    toLeaTTaMatchSubst [] = [] := rfl

@[simp] theorem toLeaTTaMatchBindings_empty :
    toLeaTTaMatchBindings Bindings.empty = [] := by
  rfl

/-- List companion to `toLeaTTaAtom_beq_self`. -/
private theorem toLeaTTaAtoms_beqList_self (es : List Atom)
    (hself : ∀ x ∈ es, (toLeaTTaAtom x == toLeaTTaAtom x) = true) :
    Metta.Atom.beqList (toLeaTTaAtoms es) (toLeaTTaAtoms es) = true := by
  induction es with
  | nil =>
      simp [toLeaTTaAtoms, Metta.Atom.beqList]
  | cons e es ihTail =>
      simp only [toLeaTTaAtoms, Metta.Atom.beqList, Bool.and_eq_true]
      constructor
      · exact hself e (List.Mem.head es)
      · exact ihTail (fun x hx => hself x (List.Mem.tail e hx))

/-- The HE->LeaTTa translation lands in the reflexive fragment of LeaTTa's
structural Boolean atom equality: no translated grounded payload is a host
float, so self-comparison reduces to `true`. -/
theorem toLeaTTaAtom_beq_self (a : Atom) :
    (toLeaTTaAtom a == toLeaTTaAtom a) = true := by
  match a with
  | .symbol s =>
      change (s == s) = true
      exact beq_self_eq_true s
  | .var v =>
      change (v == v) = true
      exact beq_self_eq_true v
  | .grounded g =>
      cases g with
      | int n =>
          change (Metta.Ground.int n == Metta.Ground.int n) = true
          change (n == n) = true
          exact beq_self_eq_true n
      | string s =>
          change (Metta.Ground.str s == Metta.Ground.str s) = true
          change (s == s) = true
          exact beq_self_eq_true s
      | bool b =>
          change (Metta.Ground.bool b == Metta.Ground.bool b) = true
          change (b == b) = true
          exact beq_self_eq_true b
      | custom typeName payload =>
          change (Metta.Ground.external typeName payload == Metta.Ground.external typeName payload) = true
          change ((typeName == typeName) && (payload == payload)) = true
          simp
  | .expression es =>
      change Metta.Atom.beqList (toLeaTTaAtoms es) (toLeaTTaAtoms es) = true
      exact toLeaTTaAtoms_beqList_self es (fun x _ => toLeaTTaAtom_beq_self x)
  termination_by sizeOf a

@[simp] theorem AssignmentsNodup.empty :
    AssignmentsNodup Bindings.empty := by
  simp [AssignmentsNodup, Bindings.empty]

theorem lookup_some_mem_assignments {xs : List (String × Atom)}
    {v : String} {a : Atom} (h : List.lookup v xs = some a) :
    (v, a) ∈ xs := by
  induction xs with
  | nil =>
      simp at h
  | cons x xs ih =>
      rcases x with ⟨k, b⟩
      by_cases hk : v == k
      · have hvk : v = k := by
          simpa using hk
        simp [List.lookup_cons, hk] at h
        subst hvk
        subst h
        simp
      · simp [List.lookup_cons, hk] at h
        simpa using Or.inr (ih h)

private theorem lookup_some_of_mem_assignment {xs : List (String × Atom)}
    {v : String} {a : Atom} (hmem : (v, a) ∈ xs) :
    ∃ a', List.lookup v xs = some a' := by
  induction xs with
  | nil =>
      cases hmem
  | cons x xs ih =>
      rcases x with ⟨k, b⟩
      simp at hmem
      rcases hmem with h | h
      · rcases h with ⟨rfl, rfl⟩
        refine ⟨a, ?_⟩
        simp
      · by_cases hk : v == k
        · exact ⟨b, by simp [List.lookup_cons, hk]⟩
        · rcases ih h with ⟨a', ha'⟩
          exact ⟨a', by simp [List.lookup_cons, hk, ha']⟩

/-- On the honest no-variable-values fragment, HE bindings are loop-free:
every successful lookup terminates immediately at a non-variable payload, so
`hasLoopFrom` can never follow an edge. This is the precise semantic reason the
restricted bridge should carry `NoVarAssignmentValues` rather than a separate
loop premise. -/
theorem NoVarAssignmentValues.hasLoop_false {b : Bindings}
    (hno : NoVarAssignmentValues b) :
    b.hasLoop = false := by
  unfold Mettapedia.Languages.MeTTa.HE.Bindings.hasLoop
  rw [List.any_eq_false]
  intro p hp
  rcases p with ⟨v, val⟩
  simp
  rcases lookup_some_of_mem_assignment hp with ⟨a', hlookup⟩
  cases a' with
  | var w =>
      exact False.elim (hno hlookup)
  | symbol s =>
      unfold Mettapedia.Languages.MeTTa.HE.Bindings.hasLoop.hasLoopFrom
      simp [Bindings.lookup, hlookup]
  | grounded g =>
      unfold Mettapedia.Languages.MeTTa.HE.Bindings.hasLoop.hasLoopFrom
      simp [Bindings.lookup, hlookup]
  | expression es =>
      unfold Mettapedia.Languages.MeTTa.HE.Bindings.hasLoop.hasLoopFrom
      simp [Bindings.lookup, hlookup]

private theorem lookup_none_not_mem_assignment_keys {xs : List (String × Atom)}
    {v : String} (h : List.lookup v xs = none) :
    v ∉ xs.map Prod.fst := by
  intro hmem
  induction xs with
  | nil =>
      simp at hmem
  | cons hd tl ih =>
      rcases hd with ⟨k, a⟩
      simp at hmem
      by_cases hk : v == k
      · simp [List.lookup_cons, hk] at h
      · have htl : List.lookup v tl = none := by
          simpa [List.lookup_cons, hk] using h
        cases hmem with
        | inl hvk =>
            apply hk
            simp [hvk]
        | inr hmemtl =>
            have hmemtl' : v ∈ tl.map Prod.fst := by
              simpa using hmemtl
            exact ih htl hmemtl'

@[simp] theorem AssignmentsNodup.assign
    {b : Bindings} {v : String} {val : Atom}
    (hkeys : AssignmentsNodup b) :
    AssignmentsNodup (b.assign v val) := by
  unfold AssignmentsNodup at hkeys ⊢
  by_cases hbound : b.isBound v
  · have hmap :
        List.map (Prod.fst ∘ fun x => if x.1 = v then (x.1, val) else x) b.assignments =
          List.map Prod.fst b.assignments := by
      induction b.assignments with
      | nil =>
          rfl
      | cons x xs ih =>
          rcases x with ⟨k, a⟩
          by_cases hk : k = v
          · simp [hk, ih]
          · simp [hk, ih]
    simp [Bindings.assign, hbound]
    rw [hmap]
    exact hkeys
  · have hlookup_none : b.lookup v = none := by
      unfold Bindings.isBound at hbound
      cases hlook : b.lookup v <;> simp [hlook] at hbound
      case none =>
        exact rfl
    have hnotmem : v ∉ b.assignments.map Prod.fst :=
      lookup_none_not_mem_assignment_keys hlookup_none
    simp [Bindings.assign, hbound]
    rw [← List.concat_eq_append]
    exact List.Nodup.concat hnotmem hkeys

/-- Successful `simpleMatch` / `simpleMatchList` preserve the no-duplicate-key
discipline of the incoming HE seed, independently of any groundness
assumption. This is the seed-shape invariant needed for transporting witnesses
into LeaTTa's matcher-facing `Bindings` surface. -/
private theorem simpleMatch_preserves_assignmentsNodup (fuel : Nat) :
    (∀ pattern target b qb,
      AssignmentsNodup b →
      simpleMatch pattern target b fuel = some qb →
        AssignmentsNodup qb) ∧
    (∀ ps ts b qb,
      AssignmentsNodup b →
      simpleMatch.simpleMatchList ps ts b fuel = some qb →
        AssignmentsNodup qb) := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro pattern target b qb _ hmatch
        simp [simpleMatch] at hmatch
      · intro ps ts b qb hkeys hmatch
        cases ps <;> cases ts <;>
          simp [simpleMatch.simpleMatchList, simpleMatch] at hmatch
        subst hmatch
        exact hkeys
  | succ n ih =>
      obtain ⟨ihAtom, ihList⟩ := ih
      have hAtomSucc :
          ∀ pattern target b qb,
            AssignmentsNodup b →
            simpleMatch pattern target b (n + 1) = some qb →
              AssignmentsNodup qb := by
        intro pattern target b qb hkeys hmatch
        cases pattern with
        | var v =>
            cases hlookup : b.lookup v with
            | none =>
                simp [simpleMatch, hlookup] at hmatch
                subst hmatch
                exact AssignmentsNodup.assign hkeys
            | some existing =>
                simp [simpleMatch, hlookup] at hmatch
                obtain ⟨_, rfl⟩ := hmatch
                exact hkeys
        | symbol s =>
            cases target <;> simp [simpleMatch] at hmatch
            obtain ⟨_, rfl⟩ := hmatch
            exact hkeys
        | grounded g =>
            cases target <;> simp [simpleMatch] at hmatch
            obtain ⟨_, rfl⟩ := hmatch
            exact hkeys
        | expression ps =>
            cases target <;> simp [simpleMatch] at hmatch
            exact ihList ps _ b qb hkeys hmatch.2
      have hListSucc :
          ∀ ps ts b qb,
            AssignmentsNodup b →
            simpleMatch.simpleMatchList ps ts b (n + 1) = some qb →
              AssignmentsNodup qb := by
        intro ps
        induction ps with
        | nil =>
            intro ts b qb hkeys hmatch
            cases ts <;> simp [simpleMatch.simpleMatchList] at hmatch
            subst hmatch
            exact hkeys
        | cons p ps ihPs =>
            intro ts b qb hkeys hmatch
            cases ts with
            | nil =>
                simp [simpleMatch.simpleMatchList] at hmatch
            | cons t ts =>
                unfold simpleMatch.simpleMatchList at hmatch
                cases hhd : simpleMatch p t b (n + 1) with
                | none =>
                    simp [hhd] at hmatch
                | some b' =>
                    simp [hhd] at hmatch
                    exact ihPs ts b' qb (hAtomSucc p t b b' hkeys hhd) hmatch
      exact ⟨hAtomSucc, hListSucc⟩

private theorem subst_lookup_erase_of_ne (s : Metta.Subst) {x v : String}
    (h : (v == x) = false) :
    Metta.Subst.lookup (Metta.Subst.erase s x) v = Metta.Subst.lookup s v := by
  induction s with
  | nil =>
      rfl
  | cons p s ih =>
      rcases p with ⟨y, a⟩
      cases hkeep : (y != x) with
      | false =>
          have hyx : y = x := by
            by_contra hyx
            have : (y != x) = true := by
              simp [hyx]
            simp [this] at hkeep
          subst hyx
          simp [Metta.Subst.erase, Metta.Subst.lookup, h]
          exact ih
      | true =>
          cases hvy : (v == y) with
          | true =>
              simp [Metta.Subst.erase, Metta.Subst.lookup, hkeep, hvy]
          | false =>
              simpa [Metta.Subst.erase, Metta.Subst.lookup, hkeep, hvy] using ih

/-- Ground HE bindings never bind a variable to another variable. This is the
precise fragment on which recursive HE lookup collapses to LeaTTa's single-pass
substitution. -/
theorem noVarAssignmentValues_of_groundBindings {b : Bindings}
    (hb : GroundBindings b) :
    NoVarAssignmentValues b := by
  intro v x hlookup
  have hmem : (v, .var x) ∈ b.assignments :=
    lookup_some_mem_assignments hlookup
  have hground : GroundAtom (.var x) := hb.1 (v, .var x) hmem
  exact (GroundAtom.not_var hground).elim

/-- Ground, key-unique seeds stay ground and key-unique under successful
`simpleMatch` / `simpleMatchList` on ground targets. This is the structural
invariant the restricted equation-step bridge uses later. -/
theorem simpleMatch_groundCanon (fuel : Nat) :
    (∀ pattern target b qb,
      GroundBindings b →
      AssignmentsNodup b →
      GroundAtom target →
      simpleMatch pattern target b fuel = some qb →
        GroundBindings qb ∧ AssignmentsNodup qb) ∧
    (∀ ps ts b qb,
      GroundBindings b →
      AssignmentsNodup b →
      (∀ t ∈ ts, GroundAtom t) →
      simpleMatch.simpleMatchList ps ts b fuel = some qb →
        GroundBindings qb ∧ AssignmentsNodup qb) := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro pattern target b qb _ _ _ hmatch
        simp [simpleMatch] at hmatch
      · intro ps ts b qb hb hkeys hground hmatch
        cases ps with
        | nil =>
            cases ts with
            | nil =>
                simp [simpleMatch.simpleMatchList] at hmatch
                subst hmatch
                exact ⟨hb, hkeys⟩
            | cons t ts =>
                simp [simpleMatch.simpleMatchList] at hmatch
        | cons p ps =>
            cases ts with
            | nil =>
                simp [simpleMatch.simpleMatchList] at hmatch
            | cons t ts =>
                simp [simpleMatch.simpleMatchList, simpleMatch] at hmatch
  | succ n ih =>
      obtain ⟨ihAtom, ihList⟩ := ih
      have hAtomSucc :
          ∀ pattern target b qb,
            GroundBindings b →
            AssignmentsNodup b →
            GroundAtom target →
            simpleMatch pattern target b (Nat.succ n) = some qb →
              GroundBindings qb ∧ AssignmentsNodup qb := by
        intro pattern target b qb hb hkeys hground hmatch
        cases pattern with
        | var v =>
            cases hlookup : b.lookup v with
            | none =>
                simp [simpleMatch, hlookup] at hmatch
                subst hmatch
                exact ⟨GroundBindings.assign hb hground, AssignmentsNodup.assign hkeys⟩
            | some existing =>
                simp [simpleMatch, hlookup] at hmatch
                obtain ⟨_, rfl⟩ := hmatch
                exact ⟨hb, hkeys⟩
        | symbol s =>
            cases target <;> simp [simpleMatch] at hmatch
            obtain ⟨_, rfl⟩ := hmatch
            exact ⟨hb, hkeys⟩
        | grounded g =>
            cases target <;> simp [simpleMatch] at hmatch
            obtain ⟨_, rfl⟩ := hmatch
            exact ⟨hb, hkeys⟩
        | expression ps =>
            cases target with
            | symbol s =>
                simp [simpleMatch] at hmatch
            | var v =>
                cases (GroundAtom.not_var (v := v) hground)
            | grounded g =>
                simp [simpleMatch] at hmatch
            | expression ts =>
                simp [simpleMatch] at hmatch
                have hgroundTs : ∀ t ∈ ts, GroundAtom t := by
                  intro t ht
                  exact GroundAtom.elem hground ht
                exact ihList ps ts b qb hb hkeys hgroundTs hmatch.2
      have hListSucc :
          ∀ ps ts b qb,
            GroundBindings b →
            AssignmentsNodup b →
            (∀ t ∈ ts, GroundAtom t) →
            simpleMatch.simpleMatchList ps ts b (Nat.succ n) = some qb →
              GroundBindings qb ∧ AssignmentsNodup qb := by
        intro ps ts b qb hb hkeys hground hmatch
        induction ps generalizing ts b qb with
        | nil =>
            cases ts <;> simp [simpleMatch.simpleMatchList] at hmatch
            subst hmatch
            exact ⟨hb, hkeys⟩
        | cons p ps ihPs =>
            cases ts with
            | nil =>
                simp [simpleMatch.simpleMatchList] at hmatch
            | cons t ts =>
                unfold simpleMatch.simpleMatchList at hmatch
                cases hhd : simpleMatch p t b (Nat.succ n) with
                | none =>
                    simp [hhd] at hmatch
                | some b' =>
                    simp [hhd] at hmatch
                    have hgroundHead : GroundAtom t := hground t (by simp)
                    have hgroundTail : ∀ t' ∈ ts, GroundAtom t' := by
                      intro t' ht'
                      exact hground t' (by simp [ht'])
                    have hb' : GroundBindings b' :=
                      (hAtomSucc p t b b' hb hkeys hgroundHead hhd).1
                    have hkeys' : AssignmentsNodup b' :=
                      (hAtomSucc p t b b' hb hkeys hgroundHead hhd).2
                    exact ihPs ts b' qb hb' hkeys' hgroundTail hmatch
      exact ⟨hAtomSucc, hListSucc⟩

/-- Successful `simpleMatch` against a ground target produces ground bindings,
starting from the empty seed. -/
theorem simpleMatch_groundBindings
    {pattern target : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : simpleMatch pattern target Bindings.empty fuel = some qb) :
    GroundBindings qb :=
  (simpleMatch_groundCanon fuel).1 pattern target Bindings.empty qb
    GroundBindings.empty AssignmentsNodup.empty hground hmatch |>.1

/-- Successful `simpleMatch` preserves the no-duplicate-key discipline from the
empty seed. -/
theorem simpleMatch_assignmentsNodup
    {pattern target : Atom} {qb : Bindings} {fuel : Nat}
    (hmatch : simpleMatch pattern target Bindings.empty fuel = some qb) :
    AssignmentsNodup qb :=
  (simpleMatch_preserves_assignmentsNodup fuel).1 pattern target Bindings.empty qb
    AssignmentsNodup.empty hmatch

private theorem lookup_none_of_not_mem_assignment_keys {xs : List (String × Atom)}
    {v : String} (h : v ∉ xs.map Prod.fst) :
    List.lookup v xs = none := by
  induction xs with
  | nil =>
      rfl
  | cons hd tl ih =>
      rcases hd with ⟨k, a⟩
      have hvk : v ≠ k := by
        intro hvk
        apply h
        simp [hvk]
      have htail : v ∉ tl.map Prod.fst := by
        intro hmem
        apply h
        simp [hmem]
      have hbeq : (v == k) = false := by
        simp [hvk]
      simp [List.lookup_cons, hbeq, ih htail]

private theorem lookup_eq_some_of_mem_assignment_nodup
    {xs : List (String × Atom)} (hkeys : (xs.map Prod.fst).Nodup)
    {v : String} {a : Atom} (hmem : (v, a) ∈ xs) :
    List.lookup v xs = some a := by
  induction xs with
  | nil =>
      cases hmem
  | cons hd tl ih =>
      rcases hd with ⟨k, b⟩
      simp at hmem
      have hkeys' : (tl.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hkeys).2
      cases hmem with
      | inl hEq =>
          rcases hEq with ⟨rfl, rfl⟩
          simp
      | inr hmemtl =>
          have hknot : k ∉ tl.map Prod.fst := by
            simpa using (List.nodup_cons.mp hkeys).1
          have hvk : v ≠ k := by
            intro hvk
            apply hknot
            have hvmem : v ∈ tl.map Prod.fst := by
              exact List.mem_map_of_mem hmemtl
            simpa [hvk] using hvmem
          have hbeq : (v == k) = false := by
            simp [hvk]
          simp [List.lookup_cons, hbeq, ih hkeys' hmemtl]

/-- Lookup-level absence of variable values implies syntactic absence when HE
assignment keys are unique. -/
theorem noBareVarAssignments_of_noVarAssignmentValues
    {b : Bindings} (hkeys : AssignmentsNodup b)
    (hno : NoVarAssignmentValues b) :
    NoBareVarAssignments b := by
  intro v x hmem
  apply hno
  exact lookup_eq_some_of_mem_assignment_nodup hkeys hmem

/-- Under the matcher invariant, value-relation membership in the canonical
assignment translation is exactly translated HE assignment membership. -/
theorem mem_val_toLeaTTaMatchBindings_iff
    {b : Bindings} (hbare : NoBareVarAssignments b)
    (v : String) (value : Metta.Atom) :
    Metta.BindingRel.val v value ∈ toLeaTTaMatchBindings b ↔
      ∃ heValue, (v, heValue) ∈ b.assignments ∧
        value = toLeaTTaAtom heValue := by
  rw [toLeaTTaMatchBindings_eq_map]
  constructor
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨⟨x, heValue⟩, hmem, hrel⟩
    have hmem' : (x, heValue) ∈ b.assignments := by
      simpa using hmem
    cases heValue with
    | var w => cases hrel
    | symbol s =>
        cases hrel
        exact ⟨.symbol s, hmem', rfl⟩
    | grounded g =>
        cases hrel
        exact ⟨.grounded g, hmem', rfl⟩
    | expression es =>
        cases hrel
        exact ⟨.expression es, hmem', rfl⟩
  · rintro ⟨heValue, hmem, rfl⟩
    apply List.mem_map.mpr
    refine ⟨(v, heValue), ?_, ?_⟩
    · simpa using hmem
    · cases heValue with
      | var w => exact (hbare hmem).elim
      | symbol s => rfl
      | grounded g => rfl
      | expression es => rfl

/-- No equality relation can arise from a matcher-valid HE assignment. -/
theorem eq_not_mem_toLeaTTaMatchBindings
    {b : Bindings} (hbare : NoBareVarAssignments b)
    (x y : String) :
    Metta.BindingRel.eq x y ∉ toLeaTTaMatchBindings b := by
  rw [toLeaTTaMatchBindings_eq_map]
  intro hmem
  rcases List.mem_map.mp hmem with ⟨⟨v, value⟩, hmem, hrel⟩
  have hmem' : (v, value) ∈ b.assignments := by
    simpa using hmem
  cases value with
  | var w => exact hbare hmem'
  | symbol s => cases hrel
  | grounded g => cases hrel
  | expression es => cases hrel

/-- Equality membership in the canonical explicit-equality translation is the
swapped HE edge, independently of chronology. -/
theorem mem_eq_toLeaTTaEqualityBindings_iff
    (b : Bindings) (x y : String) :
    Metta.BindingRel.eq x y ∈ toLeaTTaEqualityBindings b ↔
      (y, x) ∈ b.equalities := by
  simp [toLeaTTaEqualityBindings]

/-- The canonical full translation realizes the representation-independent
binding equivalence on every matcher-valid HE binding set. -/
theorem leaBindingRelEquiv_canonical
    {b : Bindings} (hbare : NoBareVarAssignments b) :
    LeaBindingRelEquiv b (toLeaTTaMatchBindingsFull b) := by
  constructor
  · intro v value
    rw [show toLeaTTaMatchBindingsFull b =
        toLeaTTaEqualityBindings b ++ toLeaTTaMatchBindings b from rfl,
      List.mem_append]
    have hnot : Metta.BindingRel.val v value ∉
        toLeaTTaEqualityBindings b := by
      simp [toLeaTTaEqualityBindings]
    simp only [hnot, false_or]
    exact mem_val_toLeaTTaMatchBindings_iff hbare v value
  · intro x y
    have hxy : Metta.BindingRel.eq x y ∈ toLeaTTaMatchBindingsFull b ↔
        (y, x) ∈ b.equalities := by
      simp only [toLeaTTaMatchBindingsFull, List.mem_append,
        mem_eq_toLeaTTaEqualityBindings_iff]
      simp [eq_not_mem_toLeaTTaMatchBindings hbare]
    have hyx : Metta.BindingRel.eq y x ∈ toLeaTTaMatchBindingsFull b ↔
        (x, y) ∈ b.equalities := by
      simp only [toLeaTTaMatchBindingsFull, List.mem_append,
        mem_eq_toLeaTTaEqualityBindings_iff]
      simp [eq_not_mem_toLeaTTaMatchBindings hbare]
    rw [hxy, hyx]
    aesop

/-- Lookup-oriented matcher invariants suffice for the canonical equivalence. -/
theorem leaBindingRelEquiv_canonical_of_nodup
    {b : Bindings} (hkeys : AssignmentsNodup b)
    (hno : NoVarAssignmentValues b) :
    LeaBindingRelEquiv b (toLeaTTaMatchBindingsFull b) :=
  leaBindingRelEquiv_canonical
    (noBareVarAssignments_of_noVarAssignmentValues hkeys hno)

private theorem lookup_reverse_eq_of_assignmentKeysNodup
    {xs : List (String × Atom)} (hkeys : (xs.map Prod.fst).Nodup) (v : String) :
    List.lookup v xs.reverse = List.lookup v xs := by
  cases h : List.lookup v xs with
  | none =>
      have hnot : v ∉ xs.map Prod.fst :=
        lookup_none_not_mem_assignment_keys h
      have hnotRev : v ∉ xs.reverse.map Prod.fst := by
        simpa [List.map_reverse, List.mem_reverse] using hnot
      exact lookup_none_of_not_mem_assignment_keys hnotRev
  | some a =>
      have hmem : (v, a) ∈ xs :=
        lookup_some_mem_assignments h
      have hkeysRev : (xs.reverse.map Prod.fst).Nodup := by
        simpa [List.map_reverse] using (List.nodup_reverse.mpr hkeys)
      have hmemRev : (v, a) ∈ xs.reverse := by
        simpa [List.mem_reverse] using hmem
      exact lookup_eq_some_of_mem_assignment_nodup hkeysRev hmemRev

private theorem toLeaTTaSubst_lookup_map (assigns : List (String × Atom)) (v : String) :
    Metta.Subst.lookup (assigns.map fun (x, a) => (x, toLeaTTaAtom a)) v =
      Option.map toLeaTTaAtom (List.lookup v assigns) := by
  induction assigns with
  | nil =>
      rfl
  | cons hd tl ih =>
      rcases hd with ⟨x, a⟩
      cases hbx : (v == x) with
      | true =>
          simp [Metta.Subst.lookup, List.lookup_cons, hbx]
      | false =>
          simpa [Metta.Subst.lookup, List.lookup_cons, hbx] using ih

private theorem toLeaTTaSubst_keys_nodup (assigns : List (String × Atom)) :
    ((toLeaTTaSubst assigns).map Prod.fst).Nodup := by
  induction assigns with
  | nil =>
      simp [toLeaTTaSubst]
  | cons p assigns ih =>
      rcases p with ⟨x, a⟩
      have hfiltered :
          List.Sublist
            (((toLeaTTaSubst assigns).filter (fun p => p.1 != x)).map Prod.fst)
            ((toLeaTTaSubst assigns).map Prod.fst) :=
        List.Sublist.map Prod.fst List.filter_sublist
      simp only [toLeaTTaSubst, Metta.Subst.extend, Metta.Subst.erase,
        List.map_cons, List.nodup_cons]
      exact ⟨by
        intro hmem
        rcases List.mem_map.mp hmem with ⟨p, hp, hpKey⟩
        rcases p with ⟨key, value⟩
        simp only at hpKey
        subst key
        have hkept : x != x := (List.mem_filter.mp hp).2
        simp at hkept,
        hfiltered.nodup ih⟩

@[simp] theorem toLeaTTaMatchSubst_lookup (assigns : List (String × Atom)) (v : String) :
    Metta.Subst.lookup (toLeaTTaMatchSubst assigns) v =
      Option.map toLeaTTaAtom (List.lookup v assigns.reverse) := by
  unfold toLeaTTaMatchSubst
  simpa using toLeaTTaSubst_lookup_map assigns.reverse v

/-- The canonical LeaTTa substitution reads exactly the same direct assignment
surface as HE's `Bindings.lookup`. -/
@[simp] theorem toLeaTTaSubst_lookup (assigns : List (String × Atom)) (v : String) :
    Metta.Subst.lookup (toLeaTTaSubst assigns) v =
      Option.map toLeaTTaAtom (List.lookup v assigns) := by
  induction assigns with
  | nil =>
      rfl
  | cons hd tl ih =>
      rcases hd with ⟨x, a⟩
      cases hbx : (v == x) with
      | true =>
          simp [toLeaTTaSubst, Metta.Subst.extend, Metta.Subst.lookup, List.lookup_cons, hbx]
      | false =>
          simp [toLeaTTaSubst, Metta.Subst.extend, Metta.Subst.lookup, List.lookup_cons, hbx]
          rw [subst_lookup_erase_of_ne (s := toLeaTTaSubst tl) (x := x) (v := v) hbx, ih]

/-- Direct-value projection deliberately hides bare-variable substitution
targets: `Bindings.ofSubst` preserves those as equality relations. -/
private def directSubstValue : Metta.Atom → Option Metta.Atom
  | .var _ => none
  | value => some value

private theorem subst_lookup_none_of_not_mem_keys
    {s : Metta.Subst} {v : String} (h : v ∉ s.map Prod.fst) :
    Metta.Subst.lookup s v = none := by
  induction s with
  | nil =>
      rfl
  | cons p s ih =>
      rcases p with ⟨x, a⟩
      have hvx : v ≠ x := by
        intro hvx
        apply h
        simp [hvx]
      have htail : v ∉ s.map Prod.fst := by
        intro hmem
        apply h
        simp [hmem]
      simp [Metta.Subst.lookup, hvx, ih htail]

/-- With distinct substitution keys, direct lookup through `ofSubst` is the
non-variable part of substitution lookup. Bare variables are observable via
equality-class resolution instead. -/
@[simp] theorem lookupVal_ofSubst_of_nodup
    (s : Metta.Subst) (hkeys : (s.map Prod.fst).Nodup) (v : String) :
    Metta.Bindings.lookupVal (Metta.Bindings.ofSubst s) v =
      (Metta.Subst.lookup s v).bind directSubstValue := by
  induction s with
  | nil =>
      rfl
  | cons p s ih =>
      rcases p with ⟨x, a⟩
      have hnot : x ∉ s.map Prod.fst := by
        simpa using (List.nodup_cons.mp hkeys).1
      have htail : (s.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hkeys).2
      cases hbx : (v == x) with
      | false =>
          cases a <;>
            simpa [Metta.Bindings.ofSubst, Metta.Bindings.lookupVal,
              Metta.Subst.lookup, directSubstValue, hbx] using ih htail
      | true =>
          have hvx : v = x := by simpa using hbx
          subst v
          cases a with
          | var y =>
              have hnone : Metta.Subst.lookup s x = none :=
                subst_lookup_none_of_not_mem_keys hnot
              have htailNone :
                  Metta.Bindings.lookupVal (Metta.Bindings.ofSubst s) x = none := by
                rw [ih htail, hnone]
                rfl
              simpa [Metta.Bindings.ofSubst, Metta.Bindings.lookupVal,
                Metta.Subst.lookup, directSubstValue] using htailNone
          | sym a =>
              simp [Metta.Bindings.ofSubst, Metta.Bindings.lookupVal,
                Metta.Subst.lookup, directSubstValue]
          | gnd a =>
              simp [Metta.Bindings.ofSubst, Metta.Bindings.lookupVal,
                Metta.Subst.lookup, directSubstValue]
          | expr a =>
              simp [Metta.Bindings.ofSubst, Metta.Bindings.lookupVal,
                Metta.Subst.lookup, directSubstValue]

/-- Direct lookup through translated assignments exposes exactly the
non-variable HE assignments. Variable assignments are equality relations. -/
@[simp] theorem toLeaTTaAssignmentBindings_lookupVal (b : Bindings) (v : String) :
    Metta.Bindings.lookupVal (toLeaTTaAssignmentBindings b) v =
      (Option.map toLeaTTaAtom (b.lookup v)).bind directSubstValue := by
  rw [toLeaTTaAssignmentBindings,
    lookupVal_ofSubst_of_nodup _ (toLeaTTaSubst_keys_nodup b.assignments)]
  simp [Bindings.lookup, toLeaTTaSubst_lookup]

/-- On HE bindings with unique assignment keys, the matcher-oriented LeaTTa
binding order has the same direct lookup behavior as the substitution-oriented
translation. This is the exact extensional bridge needed for transporting HE
matcher witnesses into LeaTTa matcher witnesses without losing substitution
meaning. -/
private def LeaLookupExt (b : Bindings) (lb : Metta.Bindings) : Prop :=
  ∀ v,
    (Metta.Bindings.resolve lb v).getD (.var v) =
      (Metta.Bindings.resolve (toLeaTTaMatchBindings b) v).getD (.var v)

@[simp] theorem toLeaTTaMatchBindings_lookupVal_of_nodup
    {b : Bindings} (hkeys : AssignmentsNodup b) (v : String) :
    Metta.Bindings.lookupVal (toLeaTTaMatchBindings b) v =
      (Option.map toLeaTTaAtom (b.lookup v)).bind directSubstValue := by
  unfold AssignmentsNodup at hkeys
  unfold toLeaTTaMatchBindings
  rw [lookupVal_ofSubst_of_nodup]
  · simp [Bindings.lookup, toLeaTTaMatchSubst_lookup,
      lookup_reverse_eq_of_assignmentKeysNodup hkeys]
  · simpa [toLeaTTaMatchSubst, List.map_reverse, List.map_map,
      Function.comp_def] using
      (List.nodup_reverse.mpr hkeys)

@[simp] theorem LeaLookupExt.empty :
    LeaLookupExt Bindings.empty Metta.Bindings.empty := by
  intro v
  rfl

theorem LeaLookupExt.of_nodup {b : Bindings} (_hkeys : AssignmentsNodup b) :
    LeaLookupExt b (toLeaTTaMatchBindings b) := by
  intro v
  rfl

@[simp] private theorem lookupVal_addValRaw_same
    (bs : Metta.Bindings) (v : String) (a : Metta.Atom) :
    Metta.Bindings.lookupVal (Metta.Bindings.addValRaw bs v a) v = some a := by
  simp [Metta.Bindings.addValRaw, Metta.Bindings.lookupVal]

private theorem lookupVal_removeVal_of_ne
    (bs : Metta.Bindings) {v w : String} (hvw : w ≠ v) :
    Metta.Bindings.lookupVal (Metta.Bindings.removeVal bs v) w =
      Metta.Bindings.lookupVal bs w := by
  induction bs with
  | nil =>
      rfl
  | cons r rs ih =>
      cases r with
      | val x a =>
          by_cases hvx : x = v
          · subst hvx
            simpa [Metta.Bindings.removeVal, Metta.Bindings.lookupVal, hvw] using ih
          · by_cases hwx : w = x
            · subst hwx
              simp [Metta.Bindings.removeVal, Metta.Bindings.lookupVal, hvx]
            · simpa [Metta.Bindings.removeVal, Metta.Bindings.lookupVal, hvx, hwx] using ih
      | eq x y =>
          simpa [Metta.Bindings.removeVal, Metta.Bindings.lookupVal] using ih

@[simp] private theorem lookupVal_addValRaw_of_ne
    (bs : Metta.Bindings) {v w : String} (a : Metta.Atom)
    (hvw : w ≠ v) :
    Metta.Bindings.lookupVal (Metta.Bindings.addValRaw bs v a) w =
      Metta.Bindings.lookupVal bs w := by
  simp [Metta.Bindings.addValRaw, Metta.Bindings.lookupVal, hvw,
    lookupVal_removeVal_of_ne bs hvw]

/- The retired `simpleMatch` bridge used direct insertion lemmas here. Full
equality-class resolution invalidates those lookup-only extension claims.
private def addTranslatedAssignment
    (lb : Metta.Bindings) (v : String) (val : Atom) : Metta.Bindings :=
  match val with
  | .var w => Metta.Bindings.addEqRaw lb v w
  | _ => Metta.Bindings.addValRaw lb v (toLeaTTaAtom val)

private theorem LeaLookupExt.addTranslatedAssignment_of_lookup_none
    {b : Bindings} {lb : Metta.Bindings} {v : String} {val : Atom}
    (hseed : LeaLookupExt b lb) (h : b.lookup v = none) :
    LeaLookupExt (b.assign v val) (addTranslatedAssignment lb v val) := by
  intro w
  cases val with
  | var x =>
      by_cases hw : w = v
      · subst w
        have hassign : (b.assign v (.var x)).lookup v = some (.var x) :=
          lookup_assign_of_lookup_none b v (.var x) h
        have hlbnone : Metta.Bindings.lookupVal lb v = none := by
          simpa [h] using hseed v
        rw [hassign]
        change Metta.Bindings.lookupVal (addTranslatedAssignment lb v (.var x)) v = none
        by_cases hvx : v = x
        · simpa [addTranslatedAssignment, Metta.Bindings.addEqRaw, hvx] using hlbnone
        · simpa [addTranslatedAssignment, Metta.Bindings.addEqRaw,
            Metta.Bindings.lookupVal, hvx] using hlbnone
      · rw [assign_lookup_ne b v (.var x) w hw h]
        by_cases hvx : v = x
        · simpa [addTranslatedAssignment, Metta.Bindings.addEqRaw, hvx] using hseed w
        · simpa [addTranslatedAssignment, Metta.Bindings.addEqRaw,
            Metta.Bindings.lookupVal, hvx] using hseed w
  | symbol s =>
      by_cases hw : w = v
      · subst w
        have hassign : (b.assign v (.symbol s)).lookup v = some (.symbol s) :=
          lookup_assign_of_lookup_none b v (.symbol s) h
        simp [addTranslatedAssignment, hassign, toLeaTTaAtom, directSubstValue]
      · simp only [addTranslatedAssignment]
        rw [lookupVal_addValRaw_of_ne lb (a := toLeaTTaAtom (.symbol s)) hw,
          assign_lookup_ne b v (.symbol s) w hw h]
        exact hseed w
  | grounded g =>
      by_cases hw : w = v
      · subst w
        have hassign : (b.assign v (.grounded g)).lookup v = some (.grounded g) :=
          lookup_assign_of_lookup_none b v (.grounded g) h
        simp [addTranslatedAssignment, hassign, toLeaTTaAtom, directSubstValue]
      · simp only [addTranslatedAssignment]
        rw [lookupVal_addValRaw_of_ne lb (a := toLeaTTaAtom (.grounded g)) hw,
          assign_lookup_ne b v (.grounded g) w hw h]
        exact hseed w
  | expression es =>
      by_cases hw : w = v
      · subst w
        have hassign : (b.assign v (.expression es)).lookup v = some (.expression es) :=
          lookup_assign_of_lookup_none b v (.expression es) h
        simp [addTranslatedAssignment, hassign, toLeaTTaAtom, directSubstValue]
      · simp only [addTranslatedAssignment]
        rw [lookupVal_addValRaw_of_ne lb (a := toLeaTTaAtom (.expression es)) hw,
          assign_lookup_ne b v (.expression es) w hw h]
        exact hseed w

private theorem LeaLookupExt.refl_of_lookup_some_eq
    {b : Bindings} {lb : Metta.Bindings} {v : String} {val : Atom}
    (hseed : LeaLookupExt b lb) (_h : b.lookup v = some val) :
    LeaLookupExt b lb := hseed
-/

/-- `matchAll` distributes over a `flatMap`-built accumulator, exactly as the
official HE list matcher does. This is the basic accumulator decomposition
lemma used to reason seed-by-seed about LeaTTa's matcher. -/
private theorem matchAll_flatMap_acc
    (xs ys : List Metta.Atom) {α : Type} (acc : List α)
    (f : α → List Metta.Bindings) :
    Metta.matchAll none (acc.flatMap f) xs ys =
      acc.flatMap (fun a => Metta.matchAll none (f a) xs ys) := by
  induction xs generalizing ys acc f with
  | nil =>
      cases ys <;> simp [Metta.matchAll]
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp [Metta.matchAll]
      | cons y ys =>
          simp only [Metta.matchAll]
          rw [List.flatMap_assoc]
          simpa using
            ih ys acc
              (fun a =>
                (f a).flatMap fun b =>
                  ((Metta.matchAtomsWith none x y).filter
                    (fun bindings => !bindings.hasLoop)).flatMap fun mb =>
                    Metta.Bindings.merge b mb)

/-- Membership form of `matchAll_flatMap_acc`. -/
private theorem mem_matchAll_flatMap_acc
    {α : Type} {xs ys : List Metta.Atom} {acc : List α}
    {f : α → List Metta.Bindings} {x : Metta.Bindings} :
    x ∈ Metta.matchAll none (acc.flatMap f) xs ys ↔
      ∃ a ∈ acc, x ∈ Metta.matchAll none (f a) xs ys := by
  rw [matchAll_flatMap_acc xs ys acc f]
  simp

/-- `matchAll` decomposes an arbitrary accumulator into singleton-seeded runs. -/
private theorem matchAll_seedwise
    (xs ys : List Metta.Atom) (seeds : List Metta.Bindings) :
    Metta.matchAll none seeds xs ys =
      seeds.flatMap (fun b => Metta.matchAll none [b] xs ys) := by
  simpa using
    (matchAll_flatMap_acc xs ys seeds (fun b => [b]))

/-- Membership form of `matchAll_seedwise`. -/
private theorem mem_matchAll_seedwise
    {xs ys : List Metta.Atom} {seeds : List Metta.Bindings}
    {x : Metta.Bindings} :
    x ∈ Metta.matchAll none seeds xs ys ↔
      ∃ b ∈ seeds, x ∈ Metta.matchAll none [b] xs ys := by
  rw [matchAll_seedwise xs ys seeds]
  simp

/-- If the head element of a LeaTTa list match can be matched from seed `b`
and the tail can be matched from the resulting singleton seed `[b']`, then the
whole cons-list match succeeds from `[b]`. This packages the exact seeded-list
constructor shape needed by the HE->LeaTTa bridge. -/
private theorem matchAll_cons_of_head_tail
    {x y : Metta.Atom} {xs ys : List Metta.Atom}
    {b b' qb : Metta.Bindings}
    (hhead :
      b' ∈ (Metta.matchAtoms x y).flatMap
        (fun mb => Metta.Bindings.merge b mb))
    (htail : qb ∈ Metta.matchAll none [b'] xs ys) :
    qb ∈ Metta.matchAll none [b] (x :: xs) (y :: ys) := by
  have hheadFiltered :
      b' ∈ ((Metta.matchAtomsWith none x y).filter
        (fun bindings => !bindings.hasLoop)).flatMap
          (fun mb => Metta.Bindings.merge b mb) := by
    simpa [Metta.matchAtoms] using hhead
  have hseeded :
      qb ∈ Metta.matchAll none
        (((Metta.matchAtomsWith none x y).filter
          (fun bindings => !bindings.hasLoop)).flatMap
          (fun mb => Metta.Bindings.merge b mb)) xs ys := by
    rw [matchAll_seedwise xs ys
      (((Metta.matchAtomsWith none x y).filter
        (fun bindings => !bindings.hasLoop)).flatMap
        (fun mb => Metta.Bindings.merge b mb))]
    exact List.mem_flatMap.mpr ⟨b', hheadFiltered, htail⟩
  simpa [Metta.matchAll] using hseeded

/-- Folding LeaTTa's `mergeOne` over a `flatMap`-built accumulator distributes
seed-by-seed. This is the merge-layer analogue of `matchAll_flatMap_acc`. -/
private theorem mergeOne_flatMap_acc
    {α : Type} (acc : List α) (f : α → List Metta.Bindings)
    (r : Metta.BindingRel) :
    Metta.Bindings.mergeOne (acc.flatMap f) r =
      acc.flatMap (fun a => Metta.Bindings.mergeOne (f a) r) := by
  simp [Metta.Bindings.mergeOne, List.flatMap_assoc]

/-- Folding LeaTTa's `mergeOne` over a `flatMap`-built accumulator distributes
seed-by-seed. This is the merge-layer analogue of `matchAll_flatMap_acc`. -/
private theorem merge_flatMap_acc
    (rs : Metta.Bindings) {α : Type} (acc : List α)
    (f : α → List Metta.Bindings) :
    rs.foldl Metta.Bindings.mergeOne (acc.flatMap f) =
      acc.flatMap (fun a => rs.foldl Metta.Bindings.mergeOne (f a)) := by
  induction rs generalizing acc f with
  | nil =>
      simp
  | cons r rs ih =>
      simp only [List.foldl_cons]
      rw [mergeOne_flatMap_acc]
      exact ih _ _

/-- `merge` decomposes any seed list into singleton-seeded merges. -/
private theorem merge_seedwise
    (right : Metta.Bindings) (seeds : List Metta.Bindings) :
    right.foldl Metta.Bindings.mergeOne seeds =
      seeds.flatMap (fun b => right.foldl Metta.Bindings.mergeOne [b]) := by
  simpa using
    (merge_flatMap_acc right seeds (fun b => [b]))

/-- Sequential LeaTTa merges collapse to a single merge over concatenated right
binding relations. This is the key algebraic simplification behind the seeded
QUERY witness factorization. -/
private theorem merge_compose
    (left mid right : Metta.Bindings) :
    (Metta.Bindings.merge left mid).flatMap
        (fun merged => Metta.Bindings.merge merged right) =
      Metta.Bindings.merge left (mid ++ right) := by
  unfold Metta.Bindings.merge
  rw [← merge_seedwise right (mid.foldl Metta.Bindings.mergeOne [left])]
  simp [List.foldl_append]

/-- Representation-independent equality for LeaTTa binding sets: every
variable has the same full equality-class readout, with an unresolved variable
observed as itself. -/
def LeaBindingsLookupEq (bs₁ bs₂ : Metta.Bindings) : Prop :=
  ∀ v,
    (Metta.Bindings.resolve bs₁ v).getD (.var v) =
      (Metta.Bindings.resolve bs₂ v).getD (.var v)

theorem LeaBindingsLookupEq.refl (bs : Metta.Bindings) :
    LeaBindingsLookupEq bs bs := by
  intro v
  rfl

theorem LeaBindingsLookupEq.symm {bs₁ bs₂ : Metta.Bindings}
    (h : LeaBindingsLookupEq bs₁ bs₂) :
    LeaBindingsLookupEq bs₂ bs₁ := by
  intro v
  exact (h v).symm

theorem LeaBindingsLookupEq.trans {bs₁ bs₂ bs₃ : Metta.Bindings}
    (h₁₂ : LeaBindingsLookupEq bs₁ bs₂)
    (h₂₃ : LeaBindingsLookupEq bs₂ bs₃) :
    LeaBindingsLookupEq bs₁ bs₃ := by
  intro v
  exact (h₁₂ v).trans (h₂₃ v)

theorem LeaBindingsLookupEq.instantiate {bs₁ bs₂ : Metta.Bindings}
    (h : LeaBindingsLookupEq bs₁ bs₂) (a : Metta.Atom) :
    Metta.instantiate bs₁ a = Metta.instantiate bs₂ a :=
  instantiate_eq_of_resolve_readout_on_vars bs₁ bs₂ a
    (fun v _ => h v)

/-- If a LeaTTa binding set has the same direct value lookups as the canonical
HE-to-LeaTTa matcher bindings for `b`, then both instantiations agree on every
translated HE atom. This lets the bridge use lookup-extensional matcher
witnesses without first proving their concrete binding-list order matches
`toLeaTTaMatchBindings b`. -/
private theorem instantiate_eq_toLeaTTaMatchBindings_of_lookupExt
    {b : Bindings} {lb : Metta.Bindings}
    (_hkeys : AssignmentsNodup b) (hlookup : LeaLookupExt b lb) :
    ∀ a : Atom,
      Metta.instantiate lb (toLeaTTaAtom a) =
        Metta.instantiate (toLeaTTaMatchBindings b) (toLeaTTaAtom a) := by
  intro a
  exact instantiate_eq_of_resolve_readout_on_vars lb
    (toLeaTTaMatchBindings b) (toLeaTTaAtom a) (fun v _ => hlookup v)

private theorem removeVal_of_lookupVal_none {bs : Metta.Bindings} {v : String}
    (h : Metta.Bindings.lookupVal bs v = none) :
    Metta.Bindings.removeVal bs v = bs := by
  induction bs with
  | nil =>
      rfl
  | cons r rs ih =>
      cases r with
      | val x a =>
          cases hvx : (v == x) with
          | true =>
              simp [Metta.Bindings.lookupVal, hvx] at h
          | false =>
              have htail : Metta.Bindings.lookupVal rs v = none := by
                simpa [Metta.Bindings.lookupVal, hvx] using h
              have hkeep : (x != v) = true := by
                by_cases hEq : x = v
                · subst hEq
                  simp at hvx
                · simp [hEq]
              simp [Metta.Bindings.removeVal, hkeep]
              simpa [Metta.Bindings.removeVal] using ih htail
      | eq x y =>
          have htail : Metta.Bindings.lookupVal rs v = none := by
            simpa [Metta.Bindings.lookupVal] using h
          simp [Metta.Bindings.removeVal]
          simpa [Metta.Bindings.removeVal] using ih htail

@[simp] theorem merge_empty_right (lb : Metta.Bindings) :
    Metta.Bindings.merge lb [] = [lb] := by
  simp [Metta.Bindings.merge]

/- These direct-lookup singleton merge lemmas belonged to the retired matcher
bridge. Class-wide consistency requires `classValues`, not `lookupVal`.
private theorem merge_singleton_val_of_lookup_none_ext
    {lb : Metta.Bindings} {v : String} {val : Metta.Atom}
    (h : Metta.Bindings.lookupVal lb v = none) :
    Metta.Bindings.merge lb [Metta.BindingRel.val v val] =
      [Metta.Bindings.addValRaw lb v val] := by
  simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, h, removeVal_of_lookupVal_none h]

private theorem merge_singleton_val_of_lookup_some_eq_ext
    {lb : Metta.Bindings} {v : String} {val : Metta.Atom}
    (h : Metta.Bindings.lookupVal lb v = some val)
    (hself : (val == val) = true) :
    Metta.Bindings.merge lb [Metta.BindingRel.val v val] = [lb] := by
  simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding, h, hself]

private theorem toLeaTTaMatchBindings_assign_of_lookup_none
    {b : Bindings} {v : String} {val : Atom}
    (hkeys : AssignmentsNodup b) (h : b.lookup v = none) :
    toLeaTTaMatchBindings (b.assign v val) =
      Metta.Bindings.addValRaw (toLeaTTaMatchBindings b) v (toLeaTTaAtom val) := by
  have hassign :
      b.assign v val = { b with assignments := b.assignments ++ [(v, val)] } := by
    simp [Bindings.assign, Bindings.isBound, h]
  rw [hassign]
  have hlookupNone : Metta.Bindings.lookupVal (toLeaTTaMatchBindings b) v = none := by
    simpa [h] using toLeaTTaMatchBindings_lookupVal_of_nodup hkeys v
  unfold toLeaTTaMatchBindings toLeaTTaMatchSubst
  simp [List.reverse_append, Metta.Bindings.addValRaw]
  change
    Metta.BindingRel.val v (toLeaTTaAtom val) ::
        Metta.Bindings.ofSubst ((List.map (fun x => (x.1, toLeaTTaAtom x.2)) b.assignments).reverse) =
      Metta.BindingRel.val v (toLeaTTaAtom val) ::
        (Metta.Bindings.ofSubst ((List.map (fun x => (x.1, toLeaTTaAtom x.2)) b.assignments).reverse)).removeVal v
  congr 1
  simpa [toLeaTTaMatchBindings, toLeaTTaMatchSubst] using
    (removeVal_of_lookupVal_none hlookupNone).symm

private theorem merge_singleton_val_of_lookup_none
    {b : Bindings} {v : String} {val : Atom}
    (hkeys : AssignmentsNodup b) (h : b.lookup v = none) :
    Metta.Bindings.merge (toLeaTTaMatchBindings b)
        [Metta.BindingRel.val v (toLeaTTaAtom val)] =
      [toLeaTTaMatchBindings (b.assign v val)] := by
  have hlookupNone : Metta.Bindings.lookupVal (toLeaTTaMatchBindings b) v = none := by
    simpa [h] using toLeaTTaMatchBindings_lookupVal_of_nodup hkeys v
  rw [merge_singleton_val_of_lookup_none_ext hlookupNone]
  exact congrArg List.singleton
    (toLeaTTaMatchBindings_assign_of_lookup_none hkeys h).symm

private theorem merge_singleton_val_of_lookup_some_eq
    {b : Bindings} {v : String} {val : Atom}
    (hkeys : AssignmentsNodup b) (h : b.lookup v = some val) :
    Metta.Bindings.merge (toLeaTTaMatchBindings b)
        [Metta.BindingRel.val v (toLeaTTaAtom val)] =
      [toLeaTTaMatchBindings b] := by
  have hlookup : Metta.Bindings.lookupVal (toLeaTTaMatchBindings b) v = some (toLeaTTaAtom val) := by
    simpa [h] using toLeaTTaMatchBindings_lookupVal_of_nodup hkeys v
  exact merge_singleton_val_of_lookup_some_eq_ext hlookup (toLeaTTaAtom_beq_self val)

theorem leattaMergeSingletonVal_lookupEq_assign_of_lookup_none
    {b : Bindings} {v : String} {val : Atom}
    (hkeys : AssignmentsNodup b) (h : b.lookup v = none) :
    ∃ emitted,
      emitted ∈ Metta.Bindings.merge (toLeaTTaMatchBindings b)
        [Metta.BindingRel.val v (toLeaTTaAtom val)] ∧
      LeaBindingsLookupEq emitted (toLeaTTaMatchBindings (b.assign v val)) := by
  refine ⟨toLeaTTaMatchBindings (b.assign v val), ?_, LeaBindingsLookupEq.refl _⟩
  rw [merge_singleton_val_of_lookup_none hkeys h]
  simp

theorem leattaMergeSingletonVal_lookupEq_same_of_lookup_some
    {b : Bindings} {v : String} {val : Atom}
    (hkeys : AssignmentsNodup b) (h : b.lookup v = some val) :
    ∃ emitted,
      emitted ∈ Metta.Bindings.merge (toLeaTTaMatchBindings b)
        [Metta.BindingRel.val v (toLeaTTaAtom val)] ∧
      LeaBindingsLookupEq emitted (toLeaTTaMatchBindings b) := by
  refine ⟨toLeaTTaMatchBindings b, ?_, LeaBindingsLookupEq.refl _⟩
  rw [merge_singleton_val_of_lookup_some_eq hkeys h]
  simp
-/

/-
The private `simpleMatch` transport below belonged to the retired one-way
query path. Equality-preserving var/var matching makes its lookup-only claims
false; the live equation lane is transported through `matchAtoms` below.

private theorem simpleMatch_var_seeded_lookup_bridge_of_ne_self
    {target : Atom} {b qb : Bindings} {lb : Metta.Bindings} {v : String} {fuel : Nat}
    (_hkeys : AssignmentsNodup b) (hseed : LeaLookupExt b lb)
    (hnotself : target ≠ .var v)
    (hoccurs : v ∉ (toLeaTTaAtom target).vars)
    (hmatch : simpleMatch (.var v) target b fuel = some qb) :
    ∃ lb',
      lb' ∈ (Metta.matchAtoms (.var v) (toLeaTTaAtom target)).flatMap
        (fun mb => Metta.Bindings.merge lb mb) ∧
      LeaLookupExt qb lb' := by
  cases fuel with
  | zero =>
      simp [simpleMatch] at hmatch
  | succ n =>
      have hoccursEq : Metta.Subst.occurs v (toLeaTTaAtom target) = false :=
        occurs_eq_false_of_not_mem_vars v (toLeaTTaAtom target) hoccurs
      cases hlook : b.lookup v with
      | none =>
          simp [simpleMatch, hlook] at hmatch
          subst hmatch
          cases target with
          | var w =>
              by_cases hwv : w = v
              · subst hwv
                exact (hnotself rfl).elim
              · have hlbnone : Metta.Bindings.lookupVal lb v = none := by
                  simpa [hlook] using hseed v
                refine ⟨Metta.Bindings.addValRaw lb v (Metta.Atom.var w), ?_, ?_⟩
                · refine List.mem_flatMap.mpr ?_
                  refine ⟨[Metta.BindingRel.val v (Metta.Atom.var w)], ?_, ?_⟩
                  · have hneq : v ≠ w := by simpa [eq_comm] using hwv
                    simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom, hneq]
                  · rw [merge_singleton_val_of_lookup_none_ext hlbnone]
                    simp
                · exact LeaLookupExt.addValRaw_of_lookup_none hseed hlook
          | symbol s =>
              have hlbnone : Metta.Bindings.lookupVal lb v = none := by
                simpa [hlook] using hseed v
              refine ⟨Metta.Bindings.addValRaw lb v (Metta.Atom.sym s), ?_, ?_⟩
              · refine List.mem_flatMap.mpr ?_
                refine ⟨[Metta.BindingRel.val v (Metta.Atom.sym s)], ?_, ?_⟩
                · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom]
                · rw [merge_singleton_val_of_lookup_none_ext hlbnone]
                  simp
              · exact LeaLookupExt.addValRaw_of_lookup_none hseed hlook
          | grounded g =>
              have hlbnone : Metta.Bindings.lookupVal lb v = none := by
                simpa [hlook] using hseed v
              refine ⟨Metta.Bindings.addValRaw lb v (Metta.Atom.gnd (toLeaTTaGround g)), ?_, ?_⟩
              · refine List.mem_flatMap.mpr ?_
                refine ⟨[Metta.BindingRel.val v (Metta.Atom.gnd (toLeaTTaGround g))], ?_, ?_⟩
                · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom]
                · rw [merge_singleton_val_of_lookup_none_ext hlbnone]
                  simp
              · exact LeaLookupExt.addValRaw_of_lookup_none hseed hlook
          | expression es =>
              have hoccursExpr :
                  Metta.Subst.occurs v (Metta.Atom.expr (toLeaTTaAtoms es)) = false := by
                simpa [toLeaTTaAtom] using hoccursEq
              have hlbnone : Metta.Bindings.lookupVal lb v = none := by
                simpa [hlook] using hseed v
              refine ⟨Metta.Bindings.addValRaw lb v (Metta.Atom.expr (toLeaTTaAtoms es)), ?_, ?_⟩
              · refine List.mem_flatMap.mpr ?_
                refine ⟨[Metta.BindingRel.val v (Metta.Atom.expr (toLeaTTaAtoms es))], ?_, ?_⟩
                · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom, hoccursExpr]
                · rw [merge_singleton_val_of_lookup_none_ext hlbnone]
                  simp
              · exact LeaLookupExt.addValRaw_of_lookup_none hseed hlook
      | some existing =>
          by_cases hEq : existing = target
          · subst hEq
            simp [simpleMatch, hlook] at hmatch
            obtain ⟨_, rfl⟩ := hmatch
            cases existing with
            | var w =>
                by_cases hwv : w = v
                · subst hwv
                  refine ⟨lb, ?_, hseed⟩
                  refine List.mem_flatMap.mpr ?_
                  refine ⟨[], ?_, ?_⟩
                  · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom]
                  · rw [merge_empty_right]
                    simp
                · have hlb : Metta.Bindings.lookupVal lb v = some (Metta.Atom.var w) := by
                    simpa [hlook, toLeaTTaAtom] using hseed v
                  refine ⟨lb, ?_, hseed⟩
                  refine List.mem_flatMap.mpr ?_
                  refine ⟨[Metta.BindingRel.val v (Metta.Atom.var w)], ?_, ?_⟩
                  · have hneq : v ≠ w := by simpa [eq_comm] using hwv
                    simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom, hneq]
                  · rw [merge_singleton_val_of_lookup_some_eq_ext hlb (toLeaTTaAtom_beq_self (.var w))]
                    simp
            | symbol s =>
                have hlb : Metta.Bindings.lookupVal lb v = some (Metta.Atom.sym s) := by
                  simpa [hlook, toLeaTTaAtom] using hseed v
                refine ⟨lb, ?_, hseed⟩
                refine List.mem_flatMap.mpr ?_
                refine ⟨[Metta.BindingRel.val v (Metta.Atom.sym s)], ?_, ?_⟩
                · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom]
                · rw [merge_singleton_val_of_lookup_some_eq_ext hlb (toLeaTTaAtom_beq_self (.symbol s))]
                  simp
            | grounded g =>
                have hlb : Metta.Bindings.lookupVal lb v = some (Metta.Atom.gnd (toLeaTTaGround g)) := by
                  simpa [hlook, toLeaTTaAtom] using hseed v
                refine ⟨lb, ?_, hseed⟩
                refine List.mem_flatMap.mpr ?_
                refine ⟨[Metta.BindingRel.val v (Metta.Atom.gnd (toLeaTTaGround g))], ?_, ?_⟩
                · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom]
                · rw [merge_singleton_val_of_lookup_some_eq_ext hlb (toLeaTTaAtom_beq_self (.grounded g))]
                  simp
            | expression es =>
                have hoccursExpr :
                    Metta.Subst.occurs v (Metta.Atom.expr (toLeaTTaAtoms es)) = false := by
                  simpa [toLeaTTaAtom] using hoccursEq
                have hlb : Metta.Bindings.lookupVal lb v = some (Metta.Atom.expr (toLeaTTaAtoms es)) := by
                  simpa [hlook, toLeaTTaAtom] using hseed v
                refine ⟨lb, ?_, hseed⟩
                refine List.mem_flatMap.mpr ?_
                refine ⟨[Metta.BindingRel.val v (Metta.Atom.expr (toLeaTTaAtoms es))], ?_, ?_⟩
                · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom, hoccursExpr]
                · rw [merge_singleton_val_of_lookup_some_eq_ext hlb
                    (toLeaTTaAtom_beq_self (.expression es))]
                  simp
          · simp [simpleMatch, hlook, hEq] at hmatch

private theorem simpleMatch_symbol_seeded_lookup_bridge
    {target : Atom} {b qb : Bindings} {lb : Metta.Bindings} {s : String} {fuel : Nat}
    (_hkeys : AssignmentsNodup b) (hseed : LeaLookupExt b lb)
    (hmatch : simpleMatch (.symbol s) target b fuel = some qb) :
    ∃ lb',
      lb' ∈ (Metta.matchAtoms (.sym s) (toLeaTTaAtom target)).flatMap
        (fun mb => Metta.Bindings.merge lb mb) ∧
      LeaLookupExt qb lb' := by
  cases fuel with
  | zero =>
      simp [simpleMatch] at hmatch
  | succ n =>
      cases target with
      | symbol t =>
          by_cases hst : s = t
          · subst hst
            simp [simpleMatch] at hmatch
            obtain ⟨_, rfl⟩ := hmatch
            refine ⟨lb, ?_, hseed⟩
            refine List.mem_flatMap.mpr ?_
            refine ⟨[], ?_, ?_⟩
            · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom]
            · rw [merge_empty_right]
              simp
          · simp [simpleMatch, hst] at hmatch
      | var v =>
          simp [simpleMatch] at hmatch
      | grounded g =>
          simp [simpleMatch] at hmatch
      | expression es =>
          simp [simpleMatch] at hmatch

private theorem simpleMatch_grounded_seeded_lookup_bridge
    {g : GroundedValue} {target : Atom} {b qb : Bindings}
    {lb : Metta.Bindings} {fuel : Nat}
    (_hkeys : AssignmentsNodup b) (hseed : LeaLookupExt b lb)
    (hmatch : simpleMatch (.grounded g) target b fuel = some qb) :
    ∃ lb',
      lb' ∈ (Metta.matchAtoms (.gnd (toLeaTTaGround g)) (toLeaTTaAtom target)).flatMap
        (fun mb => Metta.Bindings.merge lb mb) ∧
      LeaLookupExt qb lb' := by
  cases fuel with
  | zero =>
      simp [simpleMatch] at hmatch
  | succ n =>
      cases target with
      | grounded h =>
          by_cases hgh : g = h
          · subst hgh
            simp [simpleMatch] at hmatch
            obtain ⟨_, rfl⟩ := hmatch
            refine ⟨lb, ?_, hseed⟩
            refine List.mem_flatMap.mpr ?_
            refine ⟨[], ?_, ?_⟩
            · have hself :
                  Metta.Atom.equiv (Metta.Atom.gnd (toLeaTTaGround g))
                    (Metta.Atom.gnd (toLeaTTaGround g)) = true := by
                  simpa [toLeaTTaAtom] using toLeaTTaAtom_grounded_equiv_self g
              simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom, hself]
            · rw [merge_empty_right]
              simp
          · simp [simpleMatch, hgh] at hmatch
      | symbol s =>
          simp [simpleMatch] at hmatch
      | var v =>
          simp [simpleMatch] at hmatch
      | expression es =>
          simp [simpleMatch] at hmatch

private def listVars : List Atom → Nat → List String
  | [], _ => []
  | a :: as, fuel => collectVars a fuel ++ listVars as fuel

private def AtomVarsDisjoint (pattern target : Atom) (fuel : Nat) : Prop :=
  ∀ v, v ∈ collectVars pattern fuel → v ∉ collectVars target fuel

private def ListVarsDisjoint (ps ts : List Atom) (fuel : Nat) : Prop :=
  ∀ v, v ∈ listVars ps fuel → v ∉ listVars ts fuel

/-- The v1.0.8 matcher occurs-check boundary for a variable-shaped HE pattern. -/
private def VarPatternTargetOccursFree (pattern target : Atom) : Prop :=
  ∀ v, pattern = .var v → v ∉ (toLeaTTaAtom target).vars

@[simp] private theorem listVars_nil (fuel : Nat) :
    listVars [] fuel = [] := rfl

@[simp] private theorem listVars_cons (a : Atom) (as : List Atom) (fuel : Nat) :
    listVars (a :: as) fuel = collectVars a fuel ++ listVars as fuel := rfl

private theorem listVars_eq_collectVarsList :
    ∀ es fuel, listVars es fuel = collectVars.collectVarsList es fuel := by
  intro es fuel
  induction es with
  | nil =>
      rfl
  | cons e es ih =>
      simp [listVars, collectVars.collectVarsList, ih]

private theorem atomVarsDisjoint_head
    {p : Atom} {ps : List Atom} {t : Atom} {ts : List Atom} {fuel : Nat}
    (h : ListVarsDisjoint (p :: ps) (t :: ts) fuel) :
    AtomVarsDisjoint p t fuel := by
  intro v hvp hvt
  exact h v (by simp [listVars, hvp]) (by simp [listVars, hvt])

private theorem listVarsDisjoint_tail
    {p : Atom} {ps : List Atom} {t : Atom} {ts : List Atom} {fuel : Nat}
    (h : ListVarsDisjoint (p :: ps) (t :: ts) fuel) :
    ListVarsDisjoint ps ts fuel := by
  intro v hvps hvts
  exact h v (by simp [listVars, hvps]) (by simp [listVars, hvts])

private theorem listVarsDisjoint_of_exprSucc
    {ps ts : List Atom} {fuel : Nat}
    (h : AtomVarsDisjoint (.expression ps) (.expression ts) (fuel + 1)) :
    ListVarsDisjoint ps ts fuel := by
  intro v hvp hvt
  exact h v
    (by simpa [collectVars, listVars_eq_collectVarsList] using hvp)
    (by simpa [collectVars, listVars_eq_collectVarsList] using hvt)

private theorem atomVarsDisjoint_var_ne_self
    {v : String} {target : Atom} {fuel : Nat}
    (h : AtomVarsDisjoint (.var v) target (fuel + 1)) :
    target ≠ .var v := by
  intro hEq
  subst hEq
  exact h v (by simp [collectVars]) (by simp [collectVars])

private theorem simpleMatchList_seeded_lookup_bridge_of_elem
    (fuel : Nat)
    (hElem :
      ∀ {pattern target b qb lb},
        AssignmentsNodup b →
        LeaLookupExt b lb →
        AtomVarsDisjoint pattern target fuel →
        simpleMatch pattern target b fuel = some qb →
          ∃ lb',
            lb' ∈ (Metta.matchAtoms (toLeaTTaAtom pattern) (toLeaTTaAtom target)).flatMap
              (fun mb => Metta.Bindings.merge lb mb) ∧
            LeaLookupExt qb lb') :
    (∀ {ps ts b qb lb},
      AssignmentsNodup b →
      LeaLookupExt b lb →
      ListVarsDisjoint ps ts fuel →
      simpleMatch.simpleMatchList ps ts b fuel = some qb →
        ∃ lb',
          lb' ∈ Metta.matchAll none [lb] (toLeaTTaAtoms ps) (toLeaTTaAtoms ts) ∧
          LeaLookupExt qb lb') := by
  intro ps
  induction ps with
  | nil =>
      intro ts b qb lb hkeys hseed hdisj hmatch
      cases ts with
      | nil =>
          simp [simpleMatch.simpleMatchList] at hmatch
          subst hmatch
          refine ⟨lb, ?_, hseed⟩
          simp [Metta.matchAll]
      | cons t ts =>
          simp [simpleMatch.simpleMatchList] at hmatch
  | cons p ps ihPs =>
      intro ts b qb lb hkeys hseed hdisj hmatch
      cases ts with
      | nil =>
          simp [simpleMatch.simpleMatchList] at hmatch
      | cons t ts =>
          unfold simpleMatch.simpleMatchList at hmatch
          cases hhd : simpleMatch p t b fuel with
          | none =>
              simp [hhd] at hmatch
          | some b' =>
              simp [hhd] at hmatch
              have hkeys' :
                  AssignmentsNodup b' :=
                (simpleMatch_preserves_assignmentsNodup fuel).1 p t b b' hkeys hhd
              obtain ⟨lb', hhead, hseed'⟩ :=
                hElem hkeys hseed (atomVarsDisjoint_head hdisj) hhd
              obtain ⟨lb'', htail, hseed''⟩ :=
                ihPs hkeys' hseed' (listVarsDisjoint_tail hdisj) hmatch
              refine ⟨lb'', ?_, hseed''⟩
              exact matchAll_cons_of_head_tail hhead htail

/-- Seed-sensitive LeaTTa matcher target used by the recursive HE matcher
bridge. For expression/expression pairs we keep the seeded `matchAll` surface
explicit; for all other shapes we stay on the direct `matchAtoms` surface and
thread the incoming seed through LeaTTa's merge. This is the specialized
expression factorization the equation-step bridge actually needs. -/
private def LeaSeedMatch
    (pattern target : Atom) (lb out : Metta.Bindings) : Prop :=
  match pattern, target with
  | .expression ps, .expression ts =>
      out ∈ Metta.matchAll none [lb] (toLeaTTaAtoms ps) (toLeaTTaAtoms ts)
  | _, _ =>
      out ∈ (Metta.matchAtoms (toLeaTTaAtom pattern) (toLeaTTaAtom target)).flatMap
        (fun mb => Metta.Bindings.merge lb mb)

/-- Leaf-shape success bridge from HE's seeded one-way matcher into the direct
LeaTTa matcher surface. Expression-pattern recursion is intentionally excluded
here; the recursive case lands first on seeded `matchAll`
(`simpleMatch_expr_seeded_matchAll_bridge_of_elem`) and needs a separate
factorization step back to direct expression `matchAtoms`. -/
private theorem simpleMatch_leaf_seeded_lookup_bridge_disjoint :
    ∀ fuel,
      ∀ {pattern target b qb lb},
        AssignmentsNodup b →
        LeaLookupExt b lb →
        (¬ ∃ ps, pattern = .expression ps) →
        AtomVarsDisjoint pattern target fuel →
        VarPatternTargetOccursFree pattern target →
        simpleMatch pattern target b fuel = some qb →
          ∃ lb',
            lb' ∈ (Metta.matchAtoms (toLeaTTaAtom pattern) (toLeaTTaAtom target)).flatMap
              (fun mb => Metta.Bindings.merge lb mb) ∧
            LeaLookupExt qb lb' := by
  intro fuel pattern target b qb lb hkeys hseed hnonexpr hdisj hoccurs hmatch
  cases pattern with
  | var v =>
      cases fuel with
      | zero =>
          simp [simpleMatch] at hmatch
      | succ n =>
          exact
            simpleMatch_var_seeded_lookup_bridge_of_ne_self hkeys hseed
              (atomVarsDisjoint_var_ne_self hdisj) (hoccurs v rfl) hmatch
  | symbol s =>
      exact simpleMatch_symbol_seeded_lookup_bridge hkeys hseed hmatch
  | grounded g =>
      exact simpleMatch_grounded_seeded_lookup_bridge hkeys hseed hmatch
  | expression ps =>
      exact False.elim (hnonexpr ⟨ps, rfl⟩)

/-- Exact canonical leaf bridge on the non-expression fragment: when seeded HE
matching succeeds on a leaf-shape pattern, the canonical LeaTTa matcher-facing
binding order `toLeaTTaMatchBindings qb` is itself produced by LeaTTa's direct
matcher/merge surface. This sharpens the lookup-extensional bridge to the exact
binding list shape later factorization lemmas want. -/
private theorem simpleMatch_leaf_seeded_exact_bridge_disjoint :
    ∀ fuel,
      ∀ {pattern target b qb},
        AssignmentsNodup b →
        (¬ ∃ ps, pattern = .expression ps) →
        AtomVarsDisjoint pattern target fuel →
        VarPatternTargetOccursFree pattern target →
        simpleMatch pattern target b fuel = some qb →
          toLeaTTaMatchBindings qb ∈
            (Metta.matchAtoms (toLeaTTaAtom pattern) (toLeaTTaAtom target)).flatMap
              (fun mb => Metta.Bindings.merge (toLeaTTaMatchBindings b) mb) := by
  intro fuel pattern target b qb hkeys hnonexpr hdisj hoccurs hmatch
  cases pattern with
  | var v =>
      cases fuel with
      | zero =>
          simp [simpleMatch] at hmatch
      | succ n =>
          have hoccursEq : Metta.Subst.occurs v (toLeaTTaAtom target) = false :=
            occurs_eq_false_of_not_mem_vars v (toLeaTTaAtom target) (hoccurs v rfl)
          cases hlook : b.lookup v with
          | none =>
              simp [simpleMatch, hlook] at hmatch
              subst hmatch
              cases target with
              | var w =>
                  have hneq : w ≠ v := by
                    intro hwv
                    exact (atomVarsDisjoint_var_ne_self hdisj) (by simp [hwv])
                  refine List.mem_flatMap.mpr ?_
                  refine ⟨[Metta.BindingRel.val v (.var w)], ?_, ?_⟩
                  · have hvw : v ≠ w := by
                      intro hvw
                      exact hneq hvw.symm
                    simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom, hvw]
                  · rw [show
                        Metta.Bindings.merge (toLeaTTaMatchBindings b)
                          [Metta.BindingRel.val v (.var w)] =
                            [toLeaTTaMatchBindings (b.assign v (.var w))] by
                        simpa [toLeaTTaAtom] using
                          (merge_singleton_val_of_lookup_none
                            (b := b) (v := v) (val := .var w) hkeys hlook)]
                    simp
              | symbol s =>
                  refine List.mem_flatMap.mpr ?_
                  refine ⟨[Metta.BindingRel.val v (.sym s)], ?_, ?_⟩
                  · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom]
                  · rw [show
                        Metta.Bindings.merge (toLeaTTaMatchBindings b)
                          [Metta.BindingRel.val v (.sym s)] =
                            [toLeaTTaMatchBindings (b.assign v (.symbol s))] by
                        simpa [toLeaTTaAtom] using
                          (merge_singleton_val_of_lookup_none
                            (b := b) (v := v) (val := .symbol s) hkeys hlook)]
                    simp
              | grounded g =>
                  refine List.mem_flatMap.mpr ?_
                  refine ⟨[Metta.BindingRel.val v (.gnd (toLeaTTaGround g))], ?_, ?_⟩
                  · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom]
                  · rw [show
                        Metta.Bindings.merge (toLeaTTaMatchBindings b)
                          [Metta.BindingRel.val v (.gnd (toLeaTTaGround g))] =
                            [toLeaTTaMatchBindings (b.assign v (.grounded g))] by
                        simpa [toLeaTTaAtom] using
                          (merge_singleton_val_of_lookup_none
                            (b := b) (v := v) (val := .grounded g) hkeys hlook)]
                    simp
              | expression es =>
                  have hoccursExpr :
                      Metta.Subst.occurs v (Metta.Atom.expr (toLeaTTaAtoms es)) = false := by
                    simpa [toLeaTTaAtom] using hoccursEq
                  refine List.mem_flatMap.mpr ?_
                  refine ⟨[Metta.BindingRel.val v (.expr (toLeaTTaAtoms es))], ?_, ?_⟩
                  · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom, hoccursExpr]
                  · rw [show
                        Metta.Bindings.merge (toLeaTTaMatchBindings b)
                          [Metta.BindingRel.val v (.expr (toLeaTTaAtoms es))] =
                            [toLeaTTaMatchBindings (b.assign v (.expression es))] by
                        simpa [toLeaTTaAtom] using
                          (merge_singleton_val_of_lookup_none
                            (b := b) (v := v) (val := .expression es) hkeys hlook)]
                    simp
          | some existing =>
              by_cases hEq : existing = target
              · subst hEq
                simp [simpleMatch, hlook] at hmatch
                obtain ⟨_, rfl⟩ := hmatch
                cases existing with
                | var w =>
                    by_cases hwv : w = v
                    · subst hwv
                      refine List.mem_flatMap.mpr ?_
                      refine ⟨[], ?_, ?_⟩
                      · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom]
                      · rw [merge_empty_right]
                        simp
                    · refine List.mem_flatMap.mpr ?_
                      refine ⟨[Metta.BindingRel.val v (.var w)], ?_, ?_⟩
                      · have hneq : v ≠ w := by simpa [eq_comm] using hwv
                        simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom, hneq]
                      · rw [show
                            Metta.Bindings.merge (toLeaTTaMatchBindings b)
                              [Metta.BindingRel.val v (.var w)] =
                                [toLeaTTaMatchBindings b] by
                            simpa [toLeaTTaAtom] using
                              (merge_singleton_val_of_lookup_some_eq
                                (b := b) (v := v) (val := .var w) hkeys hlook)]
                        simp
                | symbol s =>
                    refine List.mem_flatMap.mpr ?_
                    refine ⟨[Metta.BindingRel.val v (.sym s)], ?_, ?_⟩
                    · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom]
                    · rw [show
                          Metta.Bindings.merge (toLeaTTaMatchBindings b)
                            [Metta.BindingRel.val v (.sym s)] =
                              [toLeaTTaMatchBindings b] by
                          simpa [toLeaTTaAtom] using
                            (merge_singleton_val_of_lookup_some_eq
                              (b := b) (v := v) (val := .symbol s) hkeys hlook)]
                      simp
                | grounded g =>
                    refine List.mem_flatMap.mpr ?_
                    refine ⟨[Metta.BindingRel.val v (.gnd (toLeaTTaGround g))], ?_, ?_⟩
                    · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom]
                    · rw [show
                          Metta.Bindings.merge (toLeaTTaMatchBindings b)
                            [Metta.BindingRel.val v (.gnd (toLeaTTaGround g))] =
                              [toLeaTTaMatchBindings b] by
                          simpa [toLeaTTaAtom] using
                            (merge_singleton_val_of_lookup_some_eq
                              (b := b) (v := v) (val := .grounded g) hkeys hlook)]
                      simp
                | expression es =>
                    have hoccursExpr :
                        Metta.Subst.occurs v (Metta.Atom.expr (toLeaTTaAtoms es)) = false := by
                      simpa [toLeaTTaAtom] using hoccursEq
                    refine List.mem_flatMap.mpr ?_
                    refine ⟨[Metta.BindingRel.val v (.expr (toLeaTTaAtoms es))], ?_, ?_⟩
                    · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom, hoccursExpr]
                    · rw [show
                          Metta.Bindings.merge (toLeaTTaMatchBindings b)
                            [Metta.BindingRel.val v (.expr (toLeaTTaAtoms es))] =
                              [toLeaTTaMatchBindings b] by
                          simpa [toLeaTTaAtom] using
                            (merge_singleton_val_of_lookup_some_eq
                              (b := b) (v := v) (val := .expression es) hkeys hlook)]
                      simp
              · simp [simpleMatch, hlook, hEq] at hmatch
  | symbol s =>
      cases fuel with
      | zero =>
          simp [simpleMatch] at hmatch
      | succ n =>
          cases target with
          | symbol t =>
              by_cases hst : s = t
              · subst hst
                simp [simpleMatch] at hmatch
                obtain ⟨_, rfl⟩ := hmatch
                refine List.mem_flatMap.mpr ?_
                refine ⟨[], ?_, ?_⟩
                · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom]
                · rw [merge_empty_right]
                  simp
              · simp [simpleMatch, hst] at hmatch
          | var v =>
              simp [simpleMatch] at hmatch
          | grounded g =>
              simp [simpleMatch] at hmatch
          | expression es =>
              simp [simpleMatch] at hmatch
  | grounded g =>
      cases fuel with
      | zero =>
          simp [simpleMatch] at hmatch
      | succ n =>
          cases target with
          | grounded h =>
              by_cases hgh : g = h
              · subst hgh
                simp [simpleMatch] at hmatch
                obtain ⟨_, rfl⟩ := hmatch
                refine List.mem_flatMap.mpr ?_
                refine ⟨[], ?_, ?_⟩
                · have hself :
                    Metta.Atom.equiv (Metta.Atom.gnd (toLeaTTaGround g))
                      (Metta.Atom.gnd (toLeaTTaGround g)) = true := by
                    simpa [toLeaTTaAtom] using toLeaTTaAtom_grounded_equiv_self g
                  simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom, hself]
                · rw [merge_empty_right]
                  simp
              · simp [simpleMatch, hgh] at hmatch
          | symbol s =>
              simp [simpleMatch] at hmatch
          | var v =>
              simp [simpleMatch] at hmatch
          | expression es =>
              simp [simpleMatch] at hmatch
  | expression ps =>
      exact False.elim (hnonexpr ⟨ps, rfl⟩)

/-- Honest leaf-fragment exact bridge under the semantic boundary we actually
need later: the successful HE result bindings may contain expressions with
variables, but they must not bind any variable directly to another variable.
This removes the older disjointness side condition on the non-expression
fragment while still excluding the genuine chain-resolution mismatch. -/
private theorem simpleMatch_leaf_seeded_exact_bridge_noVar :
    ∀ fuel,
      ∀ {pattern target b qb},
        AssignmentsNodup b →
        NoVarAssignmentValues qb →
        (¬ ∃ ps, pattern = .expression ps) →
        VarPatternTargetOccursFree pattern target →
        simpleMatch pattern target b fuel = some qb →
          toLeaTTaMatchBindings qb ∈
            (Metta.matchAtoms (toLeaTTaAtom pattern) (toLeaTTaAtom target)).flatMap
              (fun mb => Metta.Bindings.merge (toLeaTTaMatchBindings b) mb) := by
  intro fuel pattern target b qb hkeys hno hnonexpr hoccurs hmatch
  cases pattern with
  | var v =>
      cases fuel with
      | zero =>
          simp [simpleMatch] at hmatch
      | succ n =>
          have hoccursEq : Metta.Subst.occurs v (toLeaTTaAtom target) = false :=
            occurs_eq_false_of_not_mem_vars v (toLeaTTaAtom target) (hoccurs v rfl)
          cases hlook : b.lookup v with
          | none =>
              simp [simpleMatch, hlook] at hmatch
              subst hmatch
              cases target with
              | var w =>
                  have hbad :
                      (b.assign v (.var w)).lookup v = some (.var w) := by
                    exact lookup_assign_of_lookup_none b v (.var w) hlook
                  exact False.elim (hno hbad)
              | symbol s =>
                  refine List.mem_flatMap.mpr ?_
                  refine ⟨[Metta.BindingRel.val v (.sym s)], ?_, ?_⟩
                  · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom]
                  · rw [show
                        Metta.Bindings.merge (toLeaTTaMatchBindings b)
                          [Metta.BindingRel.val v (.sym s)] =
                            [toLeaTTaMatchBindings (b.assign v (.symbol s))] by
                        simpa [toLeaTTaAtom] using
                          (merge_singleton_val_of_lookup_none
                            (b := b) (v := v) (val := .symbol s) hkeys hlook)]
                    simp
              | grounded g =>
                  refine List.mem_flatMap.mpr ?_
                  refine ⟨[Metta.BindingRel.val v (.gnd (toLeaTTaGround g))], ?_, ?_⟩
                  · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom]
                  · rw [show
                        Metta.Bindings.merge (toLeaTTaMatchBindings b)
                          [Metta.BindingRel.val v (.gnd (toLeaTTaGround g))] =
                            [toLeaTTaMatchBindings (b.assign v (.grounded g))] by
                        simpa [toLeaTTaAtom] using
                          (merge_singleton_val_of_lookup_none
                            (b := b) (v := v) (val := .grounded g) hkeys hlook)]
                    simp
              | expression es =>
                  have hoccursExpr :
                      Metta.Subst.occurs v (Metta.Atom.expr (toLeaTTaAtoms es)) = false := by
                    simpa [toLeaTTaAtom] using hoccursEq
                  refine List.mem_flatMap.mpr ?_
                  refine ⟨[Metta.BindingRel.val v (.expr (toLeaTTaAtoms es))], ?_, ?_⟩
                  · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom, hoccursExpr]
                  · rw [show
                        Metta.Bindings.merge (toLeaTTaMatchBindings b)
                          [Metta.BindingRel.val v (.expr (toLeaTTaAtoms es))] =
                            [toLeaTTaMatchBindings (b.assign v (.expression es))] by
                        simpa [toLeaTTaAtom] using
                          (merge_singleton_val_of_lookup_none
                            (b := b) (v := v) (val := .expression es) hkeys hlook)]
                    simp
          | some existing =>
              by_cases hEq : existing = target
              · subst hEq
                simp [simpleMatch, hlook] at hmatch
                obtain ⟨_, rfl⟩ := hmatch
                cases existing with
                | var w =>
                    exact False.elim (hno hlook)
                | symbol s =>
                    refine List.mem_flatMap.mpr ?_
                    refine ⟨[Metta.BindingRel.val v (.sym s)], ?_, ?_⟩
                    · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom]
                    · rw [show
                          Metta.Bindings.merge (toLeaTTaMatchBindings b)
                            [Metta.BindingRel.val v (.sym s)] =
                              [toLeaTTaMatchBindings b] by
                          simpa [toLeaTTaAtom] using
                            (merge_singleton_val_of_lookup_some_eq
                              (b := b) (v := v) (val := .symbol s) hkeys hlook)]
                      simp
                | grounded g =>
                    refine List.mem_flatMap.mpr ?_
                    refine ⟨[Metta.BindingRel.val v (.gnd (toLeaTTaGround g))], ?_, ?_⟩
                    · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom]
                    · rw [show
                          Metta.Bindings.merge (toLeaTTaMatchBindings b)
                            [Metta.BindingRel.val v (.gnd (toLeaTTaGround g))] =
                              [toLeaTTaMatchBindings b] by
                          simpa [toLeaTTaAtom] using
                            (merge_singleton_val_of_lookup_some_eq
                              (b := b) (v := v) (val := .grounded g) hkeys hlook)]
                      simp
                | expression es =>
                    have hoccursExpr :
                        Metta.Subst.occurs v (Metta.Atom.expr (toLeaTTaAtoms es)) = false := by
                      simpa [toLeaTTaAtom] using hoccursEq
                    refine List.mem_flatMap.mpr ?_
                    refine ⟨[Metta.BindingRel.val v (.expr (toLeaTTaAtoms es))], ?_, ?_⟩
                    · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom, hoccursExpr]
                    · rw [show
                          Metta.Bindings.merge (toLeaTTaMatchBindings b)
                            [Metta.BindingRel.val v (.expr (toLeaTTaAtoms es))] =
                              [toLeaTTaMatchBindings b] by
                          simpa [toLeaTTaAtom] using
                            (merge_singleton_val_of_lookup_some_eq
                              (b := b) (v := v) (val := .expression es) hkeys hlook)]
                      simp
              · simp [simpleMatch, hlook, hEq] at hmatch
  | symbol s =>
      cases fuel with
      | zero =>
          simp [simpleMatch] at hmatch
      | succ n =>
          cases target with
          | symbol t =>
              by_cases hst : s = t
              · subst hst
                simp [simpleMatch] at hmatch
                obtain ⟨_, rfl⟩ := hmatch
                refine List.mem_flatMap.mpr ?_
                refine ⟨[], ?_, ?_⟩
                · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom]
                · rw [merge_empty_right]
                  simp
              · simp [simpleMatch, hst] at hmatch
          | var v =>
              simp [simpleMatch] at hmatch
          | grounded g =>
              simp [simpleMatch] at hmatch
          | expression es =>
              simp [simpleMatch] at hmatch
  | grounded g =>
      cases fuel with
      | zero =>
          simp [simpleMatch] at hmatch
      | succ n =>
          cases target with
          | grounded h =>
              by_cases hgh : g = h
              · subst hgh
                simp [simpleMatch] at hmatch
                obtain ⟨_, rfl⟩ := hmatch
                refine List.mem_flatMap.mpr ?_
                refine ⟨[], ?_, ?_⟩
                · have hself :
                    Metta.Atom.equiv (Metta.Atom.gnd (toLeaTTaGround g))
                      (Metta.Atom.gnd (toLeaTTaGround g)) = true := by
                    simpa [toLeaTTaAtom] using toLeaTTaAtom_grounded_equiv_self g
                  simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom, hself]
                · rw [merge_empty_right]
                  simp
              · simp [simpleMatch, hgh] at hmatch
          | symbol s =>
              simp [simpleMatch] at hmatch
          | var v =>
              simp [simpleMatch] at hmatch
          | expression es =>
              simp [simpleMatch] at hmatch
  | expression ps =>
      exact False.elim (hnonexpr ⟨ps, rfl⟩)

/-- Lookup-extensional leaf bridge under the same no-variable-values boundary
as `simpleMatch_leaf_seeded_exact_bridge_noVar`. This is the exact shape the
later `queryOp` item transport wants: any LeaTTa matcher witness with the same
lookup behavior as the HE result is acceptable, so we stay on the genuine
runtime surface instead of forcing canonical binding-list equality. -/
private theorem simpleMatch_leaf_seeded_lookup_bridge_noVar :
    ∀ fuel,
      ∀ {pattern target b qb lb},
        AssignmentsNodup b →
        LeaLookupExt b lb →
        NoVarAssignmentValues qb →
        (¬ ∃ ps, pattern = .expression ps) →
        VarPatternTargetOccursFree pattern target →
        simpleMatch pattern target b fuel = some qb →
          ∃ lb',
            lb' ∈ (Metta.matchAtoms (toLeaTTaAtom pattern) (toLeaTTaAtom target)).flatMap
              (fun mb => Metta.Bindings.merge lb mb) ∧
            LeaLookupExt qb lb' := by
  intro fuel pattern target b qb lb hkeys hseed hno hnonexpr hoccurs hmatch
  cases pattern with
  | var v =>
      cases fuel with
      | zero =>
          simp [simpleMatch] at hmatch
      | succ n =>
          cases hlook : b.lookup v with
          | none =>
              simp [simpleMatch, hlook] at hmatch
              subst hmatch
              cases target with
              | var w =>
                  have hbad :
                      (b.assign v (.var w)).lookup v = some (.var w) := by
                    exact lookup_assign_of_lookup_none b v (.var w) hlook
                  exact False.elim (hno hbad)
              | symbol s =>
                  have hmatch' :
                      simpleMatch (.var v) (.symbol s) b (Nat.succ n) =
                        some (b.assign v (.symbol s)) := by
                    simp [simpleMatch, hlook]
                  exact
                    simpleMatch_var_seeded_lookup_bridge_of_ne_self
                      hkeys hseed (by simp) (hoccurs v rfl) hmatch'
              | grounded g =>
                  have hmatch' :
                      simpleMatch (.var v) (.grounded g) b (Nat.succ n) =
                        some (b.assign v (.grounded g)) := by
                    simp [simpleMatch, hlook]
                  exact
                    simpleMatch_var_seeded_lookup_bridge_of_ne_self
                      hkeys hseed (by simp) (hoccurs v rfl) hmatch'
              | expression es =>
                  have hmatch' :
                      simpleMatch (.var v) (.expression es) b (Nat.succ n) =
                        some (b.assign v (.expression es)) := by
                    simp [simpleMatch, hlook]
                  exact
                    simpleMatch_var_seeded_lookup_bridge_of_ne_self
                      hkeys hseed (by simp) (hoccurs v rfl) hmatch'
          | some existing =>
              by_cases hEq : existing = target
              · subst hEq
                simp [simpleMatch, hlook] at hmatch
                obtain ⟨_, rfl⟩ := hmatch
                cases existing with
                | var w =>
                    exact False.elim (hno hlook)
                | symbol s =>
                    have hmatch' :
                        simpleMatch (.var v) (.symbol s) b (Nat.succ n) = some b := by
                      simp [simpleMatch, hlook]
                    exact
                      simpleMatch_var_seeded_lookup_bridge_of_ne_self
                        hkeys hseed (by simp) (hoccurs v rfl) hmatch'
                | grounded g =>
                    have hmatch' :
                        simpleMatch (.var v) (.grounded g) b (Nat.succ n) = some b := by
                      simp [simpleMatch, hlook]
                    exact
                      simpleMatch_var_seeded_lookup_bridge_of_ne_self
                        hkeys hseed (by simp) (hoccurs v rfl) hmatch'
                | expression es =>
                    have hmatch' :
                        simpleMatch (.var v) (.expression es) b (Nat.succ n) = some b := by
                      simp [simpleMatch, hlook]
                    exact
                      simpleMatch_var_seeded_lookup_bridge_of_ne_self
                        hkeys hseed (by simp) (hoccurs v rfl) hmatch'
              · simp [simpleMatch, hlook, hEq] at hmatch
  | symbol s =>
      exact simpleMatch_symbol_seeded_lookup_bridge hkeys hseed hmatch
  | grounded g =>
      exact simpleMatch_grounded_seeded_lookup_bridge hkeys hseed hmatch
  | expression ps =>
      exact False.elim (hnonexpr ⟨ps, rfl⟩)

/-
/-- Recursive lookup-extensional bridge on the fragment where successful HE
matching never produces variable-valued assignments. This isolates the real
positive core needed by the later equation-step transport: we can transport the
HE witness all the way onto LeaTTa's seeded matcher surface (`LeaSeedMatch`)
without yet committing to the final expression-level factorization back to the
direct `matchAtoms` surface. -/
private theorem simpleMatch_seeded_lookup_bridge_noVar (fuel : Nat) :
    (∀ {pattern target b qb lb},
      AssignmentsNodup b →
      LeaLookupExt b lb →
      NoVarAssignmentValues qb →
      simpleMatch pattern target b fuel = some qb →
        ∃ lb',
          LeaSeedMatch pattern target lb lb' ∧
          LeaLookupExt qb lb') ∧
    (∀ {ps ts b qb lb},
      AssignmentsNodup b →
      LeaLookupExt b lb →
      NoVarAssignmentValues qb →
      simpleMatch.simpleMatchList ps ts b fuel = some qb →
        ∃ lb',
          lb' ∈ Metta.matchAll none [lb] (toLeaTTaAtoms ps) (toLeaTTaAtoms ts) ∧
          LeaLookupExt qb lb') := by
  induction fuel with
  | zero =>
      constructor
      · intro pattern target b qb lb hkeys hseed hno hmatch
        simp [simpleMatch] at hmatch
      · intro ps ts b qb lb hkeys hseed hno hmatch
        cases ps with
        | nil =>
            cases ts with
            | nil =>
                simp [simpleMatch.simpleMatchList] at hmatch
                subst hmatch
                refine ⟨lb, ?_, hseed⟩
                simp [Metta.matchAll]
            | cons t ts =>
                simp [simpleMatch.simpleMatchList] at hmatch
        | cons p ps =>
            cases ts with
            | nil =>
                simp [simpleMatch.simpleMatchList] at hmatch
            | cons t ts =>
                simp [simpleMatch.simpleMatchList, simpleMatch] at hmatch
  | succ n ih =>
      obtain ⟨ihAtom, ihList⟩ := ih
      have hAtomSucc :
          ∀ {pattern target b qb lb},
            AssignmentsNodup b →
            LeaLookupExt b lb →
            NoVarAssignmentValues qb →
            simpleMatch pattern target b (Nat.succ n) = some qb →
              ∃ lb',
                LeaSeedMatch pattern target lb lb' ∧
                LeaLookupExt qb lb' := by
        intro pattern target b qb lb hkeys hseed hno hmatch
        cases pattern with
        | var v =>
            obtain ⟨lb', hmem, hlookup⟩ :=
              simpleMatch_leaf_seeded_lookup_bridge_noVar (Nat.succ n)
                hkeys hseed hno (by simp) hmatch
            exact ⟨lb', hmem, hlookup⟩
        | symbol s =>
            obtain ⟨lb', hmem, hlookup⟩ :=
              simpleMatch_leaf_seeded_lookup_bridge_noVar (Nat.succ n)
                hkeys hseed hno (by simp) hmatch
            exact ⟨lb', hmem, hlookup⟩
        | grounded g =>
            obtain ⟨lb', hmem, hlookup⟩ :=
              simpleMatch_leaf_seeded_lookup_bridge_noVar (Nat.succ n)
                hkeys hseed hno (by simp) hmatch
            exact ⟨lb', hmem, hlookup⟩
        | expression ps =>
            cases target with
            | symbol s =>
                simp [simpleMatch] at hmatch
            | var v =>
                simp [simpleMatch] at hmatch
            | grounded g =>
                simp [simpleMatch] at hmatch
            | expression ts =>
                by_cases hlen : ps.length != ts.length
                · simp [simpleMatch, hlen] at hmatch
                · have hlist :
                    simpleMatch.simpleMatchList ps ts b n = some qb := by
                    simpa [simpleMatch, hlen] using hmatch
                  obtain ⟨lb', hmem, hlookup⟩ :=
                    ihList hkeys hseed hno hlist
                  exact ⟨lb', hmem, hlookup⟩
      have hListSucc :
          ∀ {ps ts b qb lb},
            AssignmentsNodup b →
            LeaLookupExt b lb →
            NoVarAssignmentValues qb →
            simpleMatch.simpleMatchList ps ts b (Nat.succ n) = some qb →
              ∃ lb',
                lb' ∈ Metta.matchAll none [lb] (toLeaTTaAtoms ps) (toLeaTTaAtoms ts) ∧
                LeaLookupExt qb lb' := by
        intro ps
        induction ps with
        | nil =>
            intro ts b qb lb hkeys hseed hno hmatch
            cases ts with
            | nil =>
                simp [simpleMatch.simpleMatchList] at hmatch
                subst hmatch
                refine ⟨lb, ?_, hseed⟩
                simp [Metta.matchAll]
            | cons t ts =>
                simp [simpleMatch.simpleMatchList] at hmatch
        | cons p ps ihPs =>
            intro ts b qb lb hkeys hseed hno hmatch
            cases ts with
            | nil =>
                simp [simpleMatch.simpleMatchList] at hmatch
            | cons t ts =>
                unfold simpleMatch.simpleMatchList at hmatch
                cases hhd : simpleMatch p t b (Nat.succ n) with
                | none =>
                    simp [hhd] at hmatch
                | some b' =>
                    simp [hhd] at hmatch
                    have hkeys' :
                        AssignmentsNodup b' :=
                      (simpleMatch_preserves_assignmentsNodup (Nat.succ n)).1
                        p t b b' hkeys hhd
                    have hext :
                        b'.Extends qb :=
                      (simpleMatch_extends (Nat.succ n)).2 ps ts b' qb hmatch
                    have hnoHead : NoVarAssignmentValues b' :=
                      noVarAssignmentValues_of_extends hext hno
                    obtain ⟨lb', hhead, hseed'⟩ :=
                      hAtomSucc hkeys hseed hnoHead hhd
                    obtain ⟨lb'', htail, hseed''⟩ :=
                      ihPs hkeys' hseed' hno hmatch
                    refine ⟨lb'', ?_, hseed''⟩
                    exact matchAll_cons_of_head_tail hhead htail
      exact ⟨hAtomSucc, hListSucc⟩
-/

/-- Expression-shape success bridge from HE's seeded one-way matcher into
LeaTTa's seeded list matcher, assuming the recursive element bridge. This is
the honest recursive landing zone before the later expression-level
factorization back to direct `matchAtoms`. -/
private theorem simpleMatch_expr_seeded_matchAll_bridge_of_elem
    (fuel : Nat)
    (hElem :
      ∀ {pattern target b qb lb},
        AssignmentsNodup b →
        LeaLookupExt b lb →
        AtomVarsDisjoint pattern target fuel →
        simpleMatch pattern target b fuel = some qb →
          ∃ lb',
            lb' ∈ (Metta.matchAtoms (toLeaTTaAtom pattern) (toLeaTTaAtom target)).flatMap
              (fun mb => Metta.Bindings.merge lb mb) ∧
            LeaLookupExt qb lb') :
    ∀ {ps ts b qb lb},
      AssignmentsNodup b →
      LeaLookupExt b lb →
      AtomVarsDisjoint (.expression ps) (.expression ts) (fuel + 1) →
      simpleMatch (.expression ps) (.expression ts) b (fuel + 1) = some qb →
        ∃ lb',
          LeaSeedMatch (.expression ps) (.expression ts) lb lb' ∧
          LeaLookupExt qb lb' := by
  intro ps ts b qb lb hkeys hseed hdisj hmatch
  have hlist :
      simpleMatch.simpleMatchList ps ts b fuel = some qb := by
    by_cases hlen : ps.length != ts.length
    · simp [simpleMatch, hlen] at hmatch
    · simpa [simpleMatch, hlen] using hmatch
  obtain ⟨lb', hmem, hlookup⟩ :=
    (simpleMatchList_seeded_lookup_bridge_of_elem fuel hElem)
      hkeys hseed (listVarsDisjoint_of_exprSucc hdisj) hlist
  exact ⟨lb', hmem, hlookup⟩

/-- Exact canonical list lift: if each successful element match lands the
canonical LeaTTa binding surface for that head, then successful HE list
matching lands the canonical LeaTTa binding surface for the whole list from
the corresponding singleton seed. -/
private theorem simpleMatchList_seeded_exact_bridge_of_elem
    (fuel : Nat)
    (hElem :
      ∀ {pattern target b qb},
        AssignmentsNodup b →
        AtomVarsDisjoint pattern target fuel →
        simpleMatch pattern target b fuel = some qb →
          toLeaTTaMatchBindings qb ∈
            (Metta.matchAtoms (toLeaTTaAtom pattern) (toLeaTTaAtom target)).flatMap
              (fun mb => Metta.Bindings.merge (toLeaTTaMatchBindings b) mb)) :
    ∀ {ps ts b qb},
      AssignmentsNodup b →
      ListVarsDisjoint ps ts fuel →
      simpleMatch.simpleMatchList ps ts b fuel = some qb →
        toLeaTTaMatchBindings qb ∈
          Metta.matchAll none [toLeaTTaMatchBindings b] (toLeaTTaAtoms ps) (toLeaTTaAtoms ts) := by
  intro ps
  induction ps with
  | nil =>
      intro ts b qb hkeys hdisj hmatch
      cases ts with
      | nil =>
          simp [simpleMatch.simpleMatchList] at hmatch
          subst hmatch
          simp [Metta.matchAll]
      | cons t ts =>
          simp [simpleMatch.simpleMatchList] at hmatch
  | cons p ps ihPs =>
      intro ts b qb hkeys hdisj hmatch
      cases ts with
      | nil =>
          simp [simpleMatch.simpleMatchList] at hmatch
      | cons t ts =>
          unfold simpleMatch.simpleMatchList at hmatch
          cases hhd : simpleMatch p t b fuel with
          | none =>
              simp [hhd] at hmatch
          | some b' =>
              simp [hhd] at hmatch
              have hkeys' :
                  AssignmentsNodup b' :=
                (simpleMatch_preserves_assignmentsNodup fuel).1 p t b b' hkeys hhd
              have hhead :
                  toLeaTTaMatchBindings b' ∈
                    (Metta.matchAtoms (toLeaTTaAtom p) (toLeaTTaAtom t)).flatMap
                      (fun mb => Metta.Bindings.merge (toLeaTTaMatchBindings b) mb) :=
                hElem hkeys (atomVarsDisjoint_head hdisj) hhd
              have htail :
                  toLeaTTaMatchBindings qb ∈
                    Metta.matchAll none [toLeaTTaMatchBindings b'] (toLeaTTaAtoms ps) (toLeaTTaAtoms ts) :=
                ihPs hkeys' (listVarsDisjoint_tail hdisj) hmatch
      exact matchAll_cons_of_head_tail hhead htail
-/

theorem toLeaTTaAtom_vars_nil_of_ground_core :
    ∀ {a : Atom}, GroundAtom a → (toLeaTTaAtom a).vars = [] := by
  intro a hground
  induction hground with
  | symbol s =>
      simp [toLeaTTaAtom, Metta.Atom.vars]
  | grounded g =>
      simp [toLeaTTaAtom, Metta.Atom.vars]
  | @expression es hElems ih =>
      have hlist : ∀ atoms : List Atom,
          (∀ e ∈ atoms, (toLeaTTaAtom e).vars = []) →
          ((toLeaTTaAtoms atoms).map Metta.Atom.vars).flatten = [] := by
        intro atoms
        induction atoms with
        | nil =>
            simp [toLeaTTaAtoms]
        | cons e rest ihRest =>
            intro hall
            have hhead : (toLeaTTaAtom e).vars = [] := hall e (by simp)
            have htail : ∀ e' ∈ rest, (toLeaTTaAtom e').vars = [] := by
              intro e' he'
              exact hall e' (by simp [he'])
            simp [toLeaTTaAtoms, hhead, ihRest htail]
      simpa [toLeaTTaAtom, Metta.Atom.vars] using
        hlist es (fun e he => ih e he)

private theorem closedValueBindings_ofSubst
    {s : Metta.Subst}
    (hclosed : ∀ p ∈ s, p.2.vars = []) :
    ClosedValueBindings (Metta.Bindings.ofSubst s) := by
  induction s with
  | nil =>
      exact ClosedValueBindings.nil
  | cons p s ih =>
      rcases p with ⟨x, a⟩
      have ha : a.vars = [] := hclosed (x, a) (by simp)
      have hs : ∀ p ∈ s, p.2.vars = [] := by
        intro p hp
        exact hclosed p (by simp [hp])
      cases a with
      | var y =>
          simp [Metta.Atom.vars] at ha
      | sym name =>
          exact ClosedValueBindings.val (by simp [Metta.Atom.vars]) (ih hs)
      | gnd ground =>
          exact ClosedValueBindings.val (by simp [Metta.Atom.vars]) (ih hs)
      | expr children =>
          exact ClosedValueBindings.val ha (ih hs)

private theorem valueBindings_ofSubst_of_noVar
    {s : Metta.Subst}
    (hno : ∀ p ∈ s, ∀ y, p.2 ≠ .var y) :
    ValueBindings (Metta.Bindings.ofSubst s) := by
  induction s with
  | nil =>
      exact ValueBindings.nil
  | cons p s ih =>
      rcases p with ⟨x, a⟩
      have ha : ∀ y, a ≠ .var y := hno (x, a) (by simp)
      have hs : ∀ p ∈ s, ∀ y, p.2 ≠ .var y := by
        intro p hp y
        exact hno p (by simp [hp]) y
      cases a with
      | var y =>
          exact False.elim (ha y rfl)
      | sym name =>
          exact ValueBindings.val (ih hs)
      | gnd ground =>
          exact ValueBindings.val (ih hs)
      | expr children =>
          exact ValueBindings.val (ih hs)

private theorem mem_toLeaTTaSubst_source
    {assigns : List (String × Atom)} {p : Metta.VarName × Metta.Atom}
    (hp : p ∈ toLeaTTaSubst assigns) :
    ∃ original ∈ assigns,
      p = (original.1, toLeaTTaAtom original.2) := by
  induction assigns generalizing p with
  | nil =>
      simp [toLeaTTaSubst] at hp
  | cons entry rest ih =>
      rcases entry with ⟨x, a⟩
      change p ∈ (x, toLeaTTaAtom a) ::
        Metta.Subst.erase (toLeaTTaSubst rest) x at hp
      rcases List.mem_cons.mp hp with rfl | hpErase
      · exact ⟨(x, a), by simp, rfl⟩
      · have hpRest : p ∈ toLeaTTaSubst rest :=
          (List.mem_filter.mp hpErase).1
        rcases ih hpRest with ⟨original, hrest, hpEq⟩
        exact ⟨original, by simp [hrest], hpEq⟩

private theorem toLeaTTaAssignmentBindings_closed_of_ground
    {b : Bindings} (hb : GroundBindings b) :
    ClosedValueBindings (toLeaTTaAssignmentBindings b) := by
  apply closedValueBindings_ofSubst
  intro p hp
  rcases mem_toLeaTTaSubst_source hp with ⟨original, horiginal, rfl⟩
  exact toLeaTTaAtom_vars_nil_of_ground_core (hb.1 original horiginal)

private theorem toLeaTTaMatchBindings_closed_of_ground
    {b : Bindings} (hb : GroundBindings b) :
    ClosedValueBindings (toLeaTTaMatchBindings b) := by
  apply closedValueBindings_ofSubst
  intro p hp
  unfold toLeaTTaMatchSubst at hp
  rcases List.mem_map.mp hp with ⟨original, horiginalRev, rfl⟩
  have horiginal : original ∈ b.assignments := by
    simpa [List.mem_reverse] using horiginalRev
  exact toLeaTTaAtom_vars_nil_of_ground_core (hb.1 original horiginal)

private theorem toLeaTTaMatchBindings_value_of_noVar
    {b : Bindings} (hno : NoVarAssignmentValues b)
    (hkeys : AssignmentsNodup b) :
    ValueBindings (toLeaTTaMatchBindings b) := by
  apply valueBindings_ofSubst_of_noVar
  intro p hp y hvar
  unfold toLeaTTaMatchSubst at hp
  rcases List.mem_map.mp hp with ⟨original, horiginalRev, hpEq⟩
  rcases original with ⟨x, a⟩
  simp only at hpEq
  subst p
  have horiginal : (x, a) ∈ b.assignments := by
    simpa [List.mem_reverse] using horiginalRev
  have hlookup : b.lookup x = some a :=
    lookup_eq_some_of_mem_assignment_nodup
      (by simpa [AssignmentsNodup] using hkeys) horiginal
  cases a with
  | var z =>
      exact hno hlookup
  | symbol name =>
      simp [toLeaTTaAtom] at hvar
  | grounded ground =>
      simp [toLeaTTaAtom] at hvar
  | expression children =>
      simp [toLeaTTaAtom] at hvar

@[simp] theorem instantiate_toLeaTTaAssignmentBindings
    {b : Bindings} (hb : GroundBindings b) (a : Metta.Atom) :
    Metta.instantiate (toLeaTTaAssignmentBindings b) a =
      Metta.Subst.apply (toLeaTTaSubst b.assignments) a := by
  rw [ClosedValueBindings.instantiate_eq_subst_apply
    (toLeaTTaAssignmentBindings_closed_of_ground hb)]
  have hno : NoVarAssignmentValues b :=
    noVarAssignmentValues_of_groundBindings hb
  have hlookup : ∀ v,
      Metta.Subst.lookup
          (Metta.bindingsToSubst (toLeaTTaAssignmentBindings b)) v =
        Metta.Subst.lookup (toLeaTTaSubst b.assignments) v := by
    intro v
    rw [lookup_bindingsToSubst, toLeaTTaAssignmentBindings_lookupVal,
      toLeaTTaSubst_lookup]
    cases h : b.lookup v with
    | none =>
        have hlist : List.lookup v b.assignments = none := by
          simpa [Bindings.lookup] using h
        simp [hlist]
    | some value =>
        have hlist : List.lookup v b.assignments = some value := by
          simpa [Bindings.lookup] using h
        cases value with
        | var x =>
            exact False.elim (hno h)
        | symbol name =>
            simp [hlist, directSubstValue, toLeaTTaAtom]
        | grounded ground =>
            simp [hlist, directSubstValue, toLeaTTaAtom]
        | expression children =>
            simp [hlist, directSubstValue, toLeaTTaAtom]
  induction a with
  | var x =>
      simp [Metta.Subst.apply, hlookup x]
  | expr xs ih =>
      simp only [Metta.Subst.apply]
      congr 1
      exact List.map_congr_left ih
  | _ =>
      simp [Metta.Subst.apply]

private theorem matchSubst_lookup_eq_subst_of_nodup
    {assigns : List (String × Atom)} (hkeys : (assigns.map Prod.fst).Nodup) :
    ∀ v,
      Metta.Subst.lookup (toLeaTTaMatchSubst assigns) v =
        Metta.Subst.lookup (toLeaTTaSubst assigns) v := by
  intro v
  rw [toLeaTTaMatchSubst_lookup, toLeaTTaSubst_lookup,
    lookup_reverse_eq_of_assignmentKeysNodup hkeys]

private theorem subst_apply_eq_of_lookup_eq {s₁ s₂ : Metta.Subst}
    (hlookup : ∀ v, Metta.Subst.lookup s₁ v = Metta.Subst.lookup s₂ v) :
    ∀ a : Metta.Atom, Metta.Subst.apply s₁ a = Metta.Subst.apply s₂ a := by
  intro a
  induction a with
  | var x =>
      simp [Metta.Subst.apply, hlookup x]
  | expr xs ih =>
      simp only [Metta.Subst.apply]
      congr 1
      exact List.map_congr_left ih
  | _ =>
      simp [Metta.Subst.apply]

/-- For key-unique HE bindings, the matcher-oriented LeaTTa binding surface and
the substitution-oriented surface instantiate translated HE atoms identically.
This lets later query/equation proofs use LeaTTa's concrete matcher outputs
without changing the substituted reduct. -/
theorem instantiate_toLeaTTaMatchBindings_eq_subst_of_nodup
    {b : Bindings} (hb : GroundBindings b) (hkeys : AssignmentsNodup b) (a : Atom) :
    Metta.instantiate (toLeaTTaMatchBindings b) (toLeaTTaAtom a) =
      Metta.Subst.apply (toLeaTTaSubst b.assignments) (toLeaTTaAtom a) := by
  rw [ClosedValueBindings.instantiate_eq_subst_apply
    (toLeaTTaMatchBindings_closed_of_ground hb)]
  apply subst_apply_eq_of_lookup_eq
  intro v
  rw [lookup_bindingsToSubst,
    toLeaTTaMatchBindings_lookupVal_of_nodup hkeys,
    toLeaTTaSubst_lookup]
  have hno : NoVarAssignmentValues b :=
    noVarAssignmentValues_of_groundBindings hb
  cases h : b.lookup v with
  | none =>
      have hlist : List.lookup v b.assignments = none := by
        simpa [Bindings.lookup] using h
      simp [hlist]
  | some value =>
      have hlist : List.lookup v b.assignments = some value := by
        simpa [Bindings.lookup] using h
      cases value with
      | var x =>
          exact False.elim (hno h)
      | symbol name =>
          simp [hlist, directSubstValue, toLeaTTaAtom]
      | grounded ground =>
          simp [hlist, directSubstValue, toLeaTTaAtom]
      | expression children =>
          simp [hlist, directSubstValue, toLeaTTaAtom]

theorem instantiate_toLeaTTaMatchBindings_eq_subst_of_noVar_fresh
    {b : Bindings} (hno : NoVarAssignmentValues b)
    (hkeys : AssignmentsNodup b)
    (hfresh : ValueKeysFreshForValues (toLeaTTaMatchBindings b))
    (a : Atom) :
    Metta.instantiate (toLeaTTaMatchBindings b) (toLeaTTaAtom a) =
      Metta.Subst.apply (toLeaTTaSubst b.assignments) (toLeaTTaAtom a) := by
  have hval := toLeaTTaMatchBindings_value_of_noVar hno hkeys
  rw [ValueBindings.instantiate_eq_subst_apply_of_fresh hval hfresh]
  apply subst_apply_eq_of_lookup_eq
  intro v
  rw [lookup_bindingsToSubst,
    toLeaTTaMatchBindings_lookupVal_of_nodup hkeys,
    toLeaTTaSubst_lookup]
  cases h : b.lookup v with
  | none =>
      have hlist : List.lookup v b.assignments = none := by
        simpa [Bindings.lookup] using h
      simp [hlist]
  | some value =>
      have hlist : List.lookup v b.assignments = some value := by
        simpa [Bindings.lookup] using h
      cases value with
      | var x =>
          exact False.elim (hno h)
      | symbol name =>
          simp [hlist, directSubstValue, toLeaTTaAtom]
      | grounded ground =>
          simp [hlist, directSubstValue, toLeaTTaAtom]
      | expression children =>
          simp [hlist, directSubstValue, toLeaTTaAtom]

private theorem grounds_nil (env : Metta.TypeEnv) (σ : Metta.Subst) :
    Metta.Grounds env σ [] := by
  intro x T hmem
  cases hmem

/-- LeaTTa's preservation theorem composes cleanly with the HE-to-LeaTTa
binding bridge: once the translated HE bindings ground a LeaTTa typing context
and the translated rule is typed on both sides, the matcher-oriented LeaTTa
instantiations of both sides inherit that type. This is the smallest honest
interface theorem on the SR seam: the remaining work is to prove that concrete
bridged fragments actually supply `Grounds` and the rule-typing hypotheses. -/
theorem instantiated_rule_typed_of_reduction_preserves_type
    {env : Metta.TypeEnv} {Γ : List (String × Metta.Atom)}
    {lhs rhs : Atom} {qb : Bindings} {T : Metta.Atom}
    (hσ : Metta.Grounds env (toLeaTTaSubst qb.assignments) Γ)
    (hL : Metta.WT env Γ (toLeaTTaAtom lhs) T)
    (hR : Metta.WT env Γ (toLeaTTaAtom rhs) T)
    (hb : GroundBindings qb)
    (hkeys : AssignmentsNodup qb) :
    Metta.WT env [] (Metta.instantiate (toLeaTTaMatchBindings qb) (toLeaTTaAtom lhs)) T ∧
      Metta.WT env [] (Metta.instantiate (toLeaTTaMatchBindings qb) (toLeaTTaAtom rhs)) T := by
  have htyped :=
    Metta.reduction_preserves_type
      (env := env)
      (Γ := Γ)
      (L := toLeaTTaAtom lhs)
      (R := toLeaTTaAtom rhs)
      (T := T)
      (σ := toLeaTTaSubst qb.assignments)
      hσ hL hR
  constructor
  · rw [instantiate_toLeaTTaMatchBindings_eq_subst_of_nodup hb hkeys lhs]
    exact htyped.1
  · rw [instantiate_toLeaTTaMatchBindings_eq_subst_of_nodup hb hkeys rhs]
    exact htyped.2

/-- Operational wrapper for the previous theorem: if a LeaTTa work item already
contains the translated instantiated RHS, the same item carries an explicit
empty-context LeaTTa typing judgment under the preservation hypotheses. This
keeps the bridge anchored to the executable item surface rather than stopping
at a bare substitution identity. -/
theorem typed_evalResult_item_of_reduction_preserves_type
    {items : List Metta.Minimal.Item} {prev : Metta.Minimal.Stack}
    {env : Metta.TypeEnv} {Γ : List (String × Metta.Atom)}
    {lhs rhs : Atom} {qb : Bindings} {T : Metta.Atom}
    (hitem :
      Metta.Minimal.evalResult prev
          (Metta.instantiate (toLeaTTaMatchBindings qb) (toLeaTTaAtom rhs))
          (toLeaTTaMatchBindings qb) ∈ items)
    (hσ : Metta.Grounds env (toLeaTTaSubst qb.assignments) Γ)
    (hL : Metta.WT env Γ (toLeaTTaAtom lhs) T)
    (hR : Metta.WT env Γ (toLeaTTaAtom rhs) T)
    (hb : GroundBindings qb)
    (hkeys : AssignmentsNodup qb) :
    ∃ emitted m,
      Metta.Minimal.evalResult prev emitted m ∈ items ∧
      Metta.WT env [] emitted T := by
  refine ⟨Metta.instantiate (toLeaTTaMatchBindings qb) (toLeaTTaAtom rhs),
    toLeaTTaMatchBindings qb, hitem, ?_⟩
  exact (instantiated_rule_typed_of_reduction_preserves_type hσ hL hR hb hkeys).2

private theorem hasAssignedVarAux_true_exists :
    ∀ {b : Bindings} {fuel : Nat} {a : Atom},
      b.hasAssignedVarAux fuel a = true →
        ∃ w, b.isBound w = true ∧ w ∈ (toLeaTTaAtom a).vars := by
  intro b fuel
  induction fuel with
  | zero => intro a h; simp [Bindings.hasAssignedVarAux] at h
  | succ n ih =>
      intro a h
      cases a with
      | var v =>
          exact ⟨v, by simpa [Bindings.hasAssignedVarAux] using h,
            by simp [toLeaTTaAtom, Metta.Atom.vars]⟩
      | expression es =>
          simp only [Bindings.hasAssignedVarAux] at h
          rcases List.any_eq_true.mp h with ⟨e, he, hassigned⟩
          rcases ih hassigned with ⟨w, hwBound, hwVars⟩
          refine ⟨w, hwBound, ?_⟩
          simp only [toLeaTTaAtom, Metta.Atom.vars, List.mem_flatten]
          have htranslated : toLeaTTaAtom e ∈ toLeaTTaAtoms es :=
            mem_toLeaTTaAtoms_of_mem he
          refine ⟨(toLeaTTaAtom e).vars, ?_, hwVars⟩
          exact List.mem_map.mpr ⟨toLeaTTaAtom e, htranslated, rfl⟩
      | symbol s => simp [Bindings.hasAssignedVarAux] at h
      | grounded g => simp [Bindings.hasAssignedVarAux] at h

private theorem hasAssignedVar_true_exists {b : Bindings} {a : Atom}
    (h : b.hasAssignedVar a = true) :
    ∃ w, b.isBound w = true ∧ w ∈ (toLeaTTaAtom a).vars := by
  exact hasAssignedVarAux_true_exists h

private theorem key_mem_bindingValueKeys_of_val_mem
    {b : Metta.Bindings} {x : String} {a : Metta.Atom}
    (h : Metta.BindingRel.val x a ∈ b) : x ∈ bindingValueKeys b := by
  induction b with
  | nil => cases h
  | cons relation rest ih =>
      cases relation with
      | val y value =>
          simp only [List.mem_cons] at h
          simp only [bindingValueKeys, List.mem_cons]
          rcases h with h | h
          · injection h with hxy _
            exact Or.inl hxy
          · exact Or.inr (ih h)
      | eq y z =>
          simp only [List.mem_cons] at h
          rcases h with h | h
          · cases h
          · exact ih h

private theorem val_mem_toLeaTTaMatchBindings_of_lookup
    {b : Bindings} (hno : NoVarAssignmentValues b)
    {v : String} {a : Atom} (hlookup : b.lookup v = some a) :
    Metta.BindingRel.val v (toLeaTTaAtom a) ∈ toLeaTTaMatchBindings b := by
  have hmem : (v, a) ∈ b.assignments := lookup_some_mem_assignments hlookup
  cases a with
  | var w => exact False.elim (hno hlookup)
  | symbol s =>
      unfold toLeaTTaMatchBindings Metta.Bindings.ofSubst toLeaTTaMatchSubst
      apply List.mem_map.mpr
      refine ⟨(v, toLeaTTaAtom (.symbol s)), ?_, rfl⟩
      apply List.mem_map.mpr
      exact ⟨(v, .symbol s), by simpa using hmem, rfl⟩
  | grounded g =>
      unfold toLeaTTaMatchBindings Metta.Bindings.ofSubst toLeaTTaMatchSubst
      apply List.mem_map.mpr
      refine ⟨(v, toLeaTTaAtom (.grounded g)), ?_, rfl⟩
      apply List.mem_map.mpr
      exact ⟨(v, .grounded g), by simpa using hmem, rfl⟩
  | expression es =>
      unfold toLeaTTaMatchBindings Metta.Bindings.ofSubst toLeaTTaMatchSubst
      apply List.mem_map.mpr
      refine ⟨(v, toLeaTTaAtom (.expression es)), ?_, rfl⟩
      apply List.mem_map.mpr
      exact ⟨(v, .expression es), by simpa using hmem, rfl⟩

private theorem assignmentValuesIndependent_of_noVar_fresh
    {b : Bindings} (hno : NoVarAssignmentValues b)
    (hfresh : ValueKeysFreshForValues (toLeaTTaMatchBindings b)) :
    AssignmentValuesIndependent b := by
  intro v a hlookup
  cases hassigned : b.hasAssignedVar a with
  | false => rfl
  | true =>
      rcases hasAssignedVar_true_exists hassigned with
        ⟨w, hwBound, hwVars⟩
      have hwLookup : ∃ value, b.lookup w = some value := by
        unfold Bindings.isBound at hwBound
        cases h : b.lookup w with
        | none => simp [h] at hwBound
        | some value => exact ⟨value, rfl⟩
      rcases hwLookup with ⟨value, hwLookup⟩
      have hwVal := val_mem_toLeaTTaMatchBindings_of_lookup hno hwLookup
      have hwKey := key_mem_bindingValueKeys_of_val_mem hwVal
      have haVal := val_mem_toLeaTTaMatchBindings_of_lookup hno hlookup
      exact False.elim ((hfresh w hwKey v (toLeaTTaAtom a) haVal) hwVars)

/-- On assignment-independent bindings, recursive `resolve` agrees with a
single direct lookup as soon as it has one unfold step available. -/
@[simp] theorem resolve_eq_lookup_of_assignmentValuesIndependent {b : Bindings}
    (hindependent : AssignmentValuesIndependent b) (v : String) (fuel : Nat) :
    b.resolve v (fuel + 1) = b.lookup v := by
  cases h : b.lookup v with
  | none => simp [Bindings.resolve, h]
  | some a =>
      have hstable : b.hasAssignedVar a = false := hindependent h
      simp [Bindings.resolve, Bindings.resolveAtomAux, h, hstable]

/-- First substitution correspondence lemma: on variable leaves, HE's
assignment-only application surface matches LeaTTa instantiation once we are in
the no-variable-values fragment. This is the kernel of the later ground-query
equation-step bridge. -/
theorem toLeaTTaAtom_apply_var_eq_instantiate {b : Bindings}
    (hb : GroundBindings b) (v : String) (fuel : Nat) :
    toLeaTTaAtom (b.apply (.var v) (fuel + 2)) =
      Metta.instantiate (toLeaTTaAssignmentBindings b) (.var v) := by
  rw [instantiate_toLeaTTaAssignmentBindings hb]
  simp [Bindings.apply]
  have hno : NoVarAssignmentValues b :=
    noVarAssignmentValues_of_groundBindings hb
  have hfresh : ValueKeysFreshForValues (toLeaTTaMatchBindings b) :=
    ClosedValueBindings.valueKeysFreshForValues
      (toLeaTTaMatchBindings_closed_of_ground hb)
  have hindependent := assignmentValuesIndependent_of_noVar_fresh hno hfresh
  rw [resolve_eq_lookup_of_assignmentValuesIndependent hindependent v fuel]
  simp [Metta.Subst.apply, toLeaTTaSubst_lookup]
  change toLeaTTaAtom (match b.lookup v with
      | some val => val
      | none => Atom.var v) =
    (Option.map toLeaTTaAtom (b.lookup v)).getD (Metta.Atom.var v)
  cases h : b.lookup v <;> simp [toLeaTTaAtom]

/-- With enough fuel to cover the term depth, HE's bounded substitution agrees
with LeaTTa's one-pass substitution on the no-variable-values fragment. -/
theorem toLeaTTaAtom_apply_eq_subst_of_noVarAssignmentValues {b : Bindings}
    (hno : NoVarAssignmentValues b)
    (hfresh : ValueKeysFreshForValues (toLeaTTaMatchBindings b)) :
    ∀ fuel a, atomDepth a + 2 ≤ fuel →
      toLeaTTaAtom (b.apply a fuel) =
        Metta.Subst.apply (toLeaTTaSubst b.assignments) (toLeaTTaAtom a) := by
  intro fuel
  have hindependent := assignmentValuesIndependent_of_noVar_fresh hno hfresh
  induction fuel with
  | zero =>
      intro a hdepth
      omega
  | succ fuel ih =>
      intro a hdepth
      cases fuel with
      | zero =>
          cases a <;> simp [atomDepth] at hdepth
      | succ fuel' =>
          cases a with
          | symbol s =>
              simp [Bindings.apply, Metta.Subst.apply, toLeaTTaAtom]
          | var v =>
              simp [Bindings.apply]
              rw [resolve_eq_lookup_of_assignmentValuesIndependent
                hindependent v fuel']
              simp only [toLeaTTaAtom, Metta.Subst.apply]
              rw [toLeaTTaSubst_lookup]
              change toLeaTTaAtom (match b.lookup v with
                  | some val => val
                  | none => Atom.var v) =
                (Option.map toLeaTTaAtom (b.lookup v)).getD (Metta.Atom.var v)
              cases h : b.lookup v <;> simp [toLeaTTaAtom]
          | grounded g =>
              simp [Bindings.apply, Metta.Subst.apply, toLeaTTaAtom]
          | expression es =>
              have hlist :
                  ∀ es : List Atom, listDepth es + 2 ≤ fuel' + 1 →
                    toLeaTTaAtoms (es.map (fun e => b.apply e (fuel' + 1))) =
                      (toLeaTTaAtoms es).map
                        (Metta.Subst.apply (toLeaTTaSubst b.assignments)) := by
                intro es
                induction es with
                | nil =>
                    intro _
                    rfl
                | cons e es ihEs =>
                    intro hes
                    simp [toLeaTTaAtoms, listDepth] at hes ⊢
                    have hhead : atomDepth e + 2 ≤ fuel' + 1 := by
                      omega
                    have htail : listDepth es + 2 ≤ fuel' + 1 := by
                      omega
                    constructor
                    · exact ih e hhead
                    · exact ihEs htail
              have hes : listDepth es + 2 ≤ fuel' + 1 := by
                simp [atomDepth] at hdepth
                omega
              simpa [Bindings.apply, Metta.Subst.apply, toLeaTTaAtom] using hlist es hes

/-- Ground HE bindings automatically satisfy the no-variable-values boundary,
so the bounded substitution correspondence applies whenever the fuel covers the
term depth. -/
theorem toLeaTTaAtom_apply_eq_subst_of_groundBindings {b : Bindings}
    (hb : GroundBindings b) :
    ∀ fuel a, atomDepth a + 2 ≤ fuel →
      toLeaTTaAtom (b.apply a fuel) =
        Metta.Subst.apply (toLeaTTaSubst b.assignments) (toLeaTTaAtom a) :=
  toLeaTTaAtom_apply_eq_subst_of_noVarAssignmentValues
    (noVarAssignmentValues_of_groundBindings hb)
    (ClosedValueBindings.valueKeysFreshForValues
      (toLeaTTaMatchBindings_closed_of_ground hb))

/-- Once HE bindings are both ground and key-unique, translated HE application
and LeaTTa instantiation agree even when we use LeaTTa's matcher-facing binding
order. This is the bridge form needed for transported QUERY witnesses, because
LeaTTa's concrete matcher returns `toLeaTTaMatchBindings`, not the
substitution-oriented binding order. -/
theorem toLeaTTaAtom_apply_eq_instantiate_matchBindings_of_groundBindings
    {b : Bindings} (hb : GroundBindings b) (hkeys : AssignmentsNodup b) :
    ∀ fuel a, atomDepth a + 2 ≤ fuel →
      toLeaTTaAtom (b.apply a fuel) =
        Metta.instantiate (toLeaTTaMatchBindings b) (toLeaTTaAtom a) := by
  intro fuel a hdepth
  rw [instantiate_toLeaTTaMatchBindings_eq_subst_of_nodup hb hkeys a]
  exact toLeaTTaAtom_apply_eq_subst_of_groundBindings hb fuel a hdepth

/-- Ground HE substitutions can be transported through any LeaTTa matcher
witness whose direct value lookups coincide with the HE bindings. This is the
instantiate-side counterpart to the lookup-extensional matcher bridge and is
the form the later equation-step transport actually consumes. -/
theorem toLeaTTaAtom_apply_eq_instantiate_of_groundBindings_lookupExt
    {b : Bindings} {lb : Metta.Bindings}
    (hb : GroundBindings b) (hkeys : AssignmentsNodup b)
    (hlookup : LeaLookupExt b lb) :
    ∀ fuel a, atomDepth a + 2 ≤ fuel →
      toLeaTTaAtom (b.apply a fuel) =
        Metta.instantiate lb (toLeaTTaAtom a) := by
  intro fuel a hdepth
  trans Metta.instantiate (toLeaTTaMatchBindings b) (toLeaTTaAtom a)
  · exact
      toLeaTTaAtom_apply_eq_instantiate_matchBindings_of_groundBindings
        hb hkeys fuel a hdepth
  · symm
    exact instantiate_eq_toLeaTTaMatchBindings_of_lookupExt hkeys hlookup a

/-- The matcher-facing LeaTTa binding order also agrees with HE's recursive
application on the broader no-variable-values fragment, provided assignment keys
remain unique and the fuel covers the term depth. This is the exact semantic
agreement line exposed by the chain-resolution counterexample: HE may leave
variables unbound, but it must not bind them to further variables if we want its
`apply` surface to match LeaTTa's one-pass `instantiate`. -/
theorem toLeaTTaAtom_apply_eq_instantiate_matchBindings_of_noVarAssignmentValues
    {b : Bindings} (hno : NoVarAssignmentValues b) (hkeys : AssignmentsNodup b)
    (hfresh : ValueKeysFreshForValues (toLeaTTaMatchBindings b)) :
    ∀ fuel a, atomDepth a + 2 ≤ fuel →
      toLeaTTaAtom (b.apply a fuel) =
        Metta.instantiate (toLeaTTaMatchBindings b) (toLeaTTaAtom a) := by
  intro fuel a hdepth
  rw [instantiate_toLeaTTaMatchBindings_eq_subst_of_noVar_fresh
    hno hkeys hfresh a]
  exact toLeaTTaAtom_apply_eq_subst_of_noVarAssignmentValues
    hno hfresh fuel a hdepth

/-- The no-variable-values substitution correspondence also transports through
any LeaTTa matcher witness with the same direct lookup behavior as the HE
bindings. This is the lookup-extensional form the remaining queryOp witness
transport can consume without committing to LeaTTa's concrete binding-list
order. -/
theorem toLeaTTaAtom_apply_eq_instantiate_of_noVarAssignmentValues_lookupExt
    {b : Bindings} {lb : Metta.Bindings}
    (hno : NoVarAssignmentValues b) (hkeys : AssignmentsNodup b)
    (hfresh : ValueKeysFreshForValues (toLeaTTaMatchBindings b))
    (hlookup : LeaLookupExt b lb) :
    ∀ fuel a, atomDepth a + 2 ≤ fuel →
      toLeaTTaAtom (b.apply a fuel) =
        Metta.instantiate lb (toLeaTTaAtom a) := by
  intro fuel a hdepth
  trans Metta.instantiate (toLeaTTaMatchBindings b) (toLeaTTaAtom a)
  · exact
      toLeaTTaAtom_apply_eq_instantiate_matchBindings_of_noVarAssignmentValues
        hno hkeys hfresh fuel a hdepth
  · symm
    exact instantiate_eq_toLeaTTaMatchBindings_of_lookupExt hkeys hlookup a

/-- Any exact LeaTTa item whose emitted atom is the matcher-instantiated
translation of an HE RHS already presents the visible HE successor up to
α-equivalence on the no-variable-values fragment. This is the right target for
the non-ground positive bridge: the runtime emits the instantiated RHS, not the
freshened raw RHS. -/
theorem visible_successor_of_instantiated_item
    {rhs : Atom} {qb : Bindings} {fuel : Nat} {prev : Metta.Minimal.Stack}
    {items : List Metta.Minimal.Item}
    (heq : qb.equalities = [])
    (hno : NoVarAssignmentValues qb) (hkeys : AssignmentsNodup qb)
    (hfresh : ValueKeysFreshForValues (toLeaTTaMatchBindings qb))
    (hdepth : atomDepth rhs + 2 ≤ fuel)
    (hitem :
      Metta.Minimal.evalResult prev
          (Metta.instantiate (toLeaTTaMatchBindings qb) (toLeaTTaAtom rhs))
          (toLeaTTaMatchBindings qb) ∈ items) :
    ∃ emitted m,
      Metta.Minimal.evalResult prev emitted m ∈ items ∧
      Metta.AlphaEq emitted (toLeaTTaAtom (qb.applyFull rhs fuel)) := by
  refine ⟨Metta.instantiate (toLeaTTaMatchBindings qb) (toLeaTTaAtom rhs),
    toLeaTTaMatchBindings qb, hitem, ?_⟩
  unfold Metta.AlphaEq
  rw [Bindings.applyFull_no_equalities heq]
  rw [← toLeaTTaAtom_apply_eq_instantiate_matchBindings_of_noVarAssignmentValues
    hno hkeys hfresh fuel rhs hdepth]

/-- Lookup-extensional version of the visible-successor bridge. If the emitted
runtime item instantiates the RHS using any LeaTTa matcher witness that agrees
with the HE bindings on direct lookups, that item already represents the HE
visible successor up to α-equivalence on the no-variable-values fragment. -/
theorem visible_successor_of_lookupExt_instantiated_item
    {rhs : Atom} {qb : Bindings} {fuel : Nat} {prev : Metta.Minimal.Stack}
    {items : List Metta.Minimal.Item} {lb : Metta.Bindings}
    (heq : qb.equalities = [])
    (hno : NoVarAssignmentValues qb) (hkeys : AssignmentsNodup qb)
    (hfresh : ValueKeysFreshForValues (toLeaTTaMatchBindings qb))
    (hlookup : LeaLookupExt qb lb)
    (hdepth : atomDepth rhs + 2 ≤ fuel)
    (hitem :
      Metta.Minimal.evalResult prev
          (Metta.instantiate lb (toLeaTTaAtom rhs))
          lb ∈ items) :
    ∃ emitted m,
      Metta.Minimal.evalResult prev emitted m ∈ items ∧
      Metta.AlphaEq emitted (toLeaTTaAtom (qb.applyFull rhs fuel)) := by
  refine ⟨Metta.instantiate lb (toLeaTTaAtom rhs), lb, hitem, ?_⟩
  unfold Metta.AlphaEq
  rw [Bindings.applyFull_no_equalities heq]
  rw [← toLeaTTaAtom_apply_eq_instantiate_of_noVarAssignmentValues_lookupExt
    hno hkeys hfresh hlookup fuel rhs hdepth]

/-- LeaTTa's alpha-equivalence collapses bare variable names to the same
canonical representative. This is the small reusable fact behind equality-bearing
HE transports whose visible successor is an unresolved variable: the executable
matcher may orient the equality one way, while HE may expose the other name. -/
theorem alphaEq_var_var (x y : String) :
    Metta.AlphaEq (Metta.Atom.var x) (Metta.Atom.var y) := by
  unfold Metta.AlphaEq Metta.canonicalizeVars
  simp [Metta.Atom.vars, Metta.distinctVarsAux, Metta.renameVars]

/-- If an HE visible successor is an unresolved variable, any LeaTTa executable
item emitting a variable already observes that successor up to alpha-equivalence.
This is the equality-transport counterpart to the instantiated-item lemmas above:
it avoids forcing the assignment-only projection to pick the same variable name
that HE exposes. -/
theorem visible_successor_of_variable_item
    {rhs : Atom} {qb : Bindings} {fuel : Nat} {prev : Metta.Minimal.Stack}
    {items : List Metta.Minimal.Item} {emittedVar targetVar : String}
    {m : Metta.Bindings}
    (happly : qb.applyFull rhs fuel = .var targetVar)
    (hitem : Metta.Minimal.evalResult prev (Metta.Atom.var emittedVar) m ∈ items) :
    ∃ emitted m',
      Metta.Minimal.evalResult prev emitted m' ∈ items ∧
      Metta.AlphaEq emitted (toLeaTTaAtom (qb.applyFull rhs fuel)) := by
  refine ⟨Metta.Atom.var emittedVar, m, hitem, ?_⟩
  rw [happly]
  simpa [toLeaTTaAtom] using alphaEq_var_var emittedVar targetVar

/-- Typed visible-successor bridge on the instantiated-item surface. If a LeaTTa
item already carries the translated instantiated RHS, then under the explicit
LeaTTa preservation hypotheses it simultaneously (1) represents the visible HE
successor up to α-equivalence and (2) carries the corresponding empty-context
LeaTTa typing judgment. This is the smallest honest typed simulation package on
the executable-item seam. -/
theorem typed_visible_successor_of_instantiated_item
    {rhs lhs : Atom} {qb : Bindings} {fuel : Nat} {prev : Metta.Minimal.Stack}
    {items : List Metta.Minimal.Item}
    {env : Metta.TypeEnv} {Γ : List (String × Metta.Atom)} {T : Metta.Atom}
    (hno : NoVarAssignmentValues qb) (hkeys : AssignmentsNodup qb)
    (hfresh : ValueKeysFreshForValues (toLeaTTaMatchBindings qb))
    (hb : GroundBindings qb)
    (hdepth : atomDepth rhs + 2 ≤ fuel)
    (hitem :
      Metta.Minimal.evalResult prev
          (Metta.instantiate (toLeaTTaMatchBindings qb) (toLeaTTaAtom rhs))
          (toLeaTTaMatchBindings qb) ∈ items)
    (hσ : Metta.Grounds env (toLeaTTaSubst qb.assignments) Γ)
    (hL : Metta.WT env Γ (toLeaTTaAtom lhs) T)
    (hR : Metta.WT env Γ (toLeaTTaAtom rhs) T) :
    ∃ emitted m,
      Metta.Minimal.evalResult prev emitted m ∈ items ∧
      Metta.AlphaEq emitted (toLeaTTaAtom (qb.applyFull rhs fuel)) ∧
      Metta.WT env [] emitted T := by
  refine ⟨Metta.instantiate (toLeaTTaMatchBindings qb) (toLeaTTaAtom rhs),
    toLeaTTaMatchBindings qb, hitem, ?_, ?_⟩
  · unfold Metta.AlphaEq
    rw [Bindings.applyFull_no_equalities hb.2]
    rw [← toLeaTTaAtom_apply_eq_instantiate_matchBindings_of_noVarAssignmentValues
      hno hkeys hfresh fuel rhs hdepth]
  · exact (instantiated_rule_typed_of_reduction_preserves_type hσ hL hR hb hkeys).2

/-- Once the fuel covers the atom depth, HE's bounded `collectVars` sees exactly
the same left-to-right variable multiset as LeaTTa's ordinary `Atom.vars`. This
is the bookkeeping bridge needed to compare HE freshening against LeaTTa's
`freshenRule`. -/
private theorem collectVars_eq_toLeaTTaAtom_vars_of_depth :
    ∀ fuel a, atomDepth a + 1 ≤ fuel →
      collectVars a fuel = (toLeaTTaAtom a).vars := by
  intro fuel
  induction fuel with
  | zero =>
      intro a hdepth
      omega
  | succ fuel ih =>
      intro a hdepth
      cases a with
      | symbol s =>
          simp [collectVars, toLeaTTaAtom, Metta.Atom.vars]
      | var v =>
          simp [collectVars, toLeaTTaAtom, Metta.Atom.vars]
      | grounded g =>
          simp [collectVars, toLeaTTaAtom, Metta.Atom.vars]
      | expression es =>
          have hlist :
              ∀ es : List Atom, listDepth es + 1 ≤ fuel →
                collectVars.collectVarsList es fuel =
                  ((toLeaTTaAtoms es).map Metta.Atom.vars).flatten := by
            intro es
            induction es with
            | nil =>
                intro _
                simp [collectVars.collectVarsList, toLeaTTaAtoms]
            | cons e es ihEs =>
                intro hes
                simp [collectVars.collectVarsList, toLeaTTaAtoms, listDepth] at hes ⊢
                have hhead : atomDepth e + 1 ≤ fuel := by
                  omega
                have htail : listDepth es + 1 ≤ fuel := by
                  omega
                rw [ih e hhead, ihEs htail]
          have hes : listDepth es + 1 ≤ fuel := by
            simp [atomDepth] at hdepth
            omega
          simpa [collectVars, toLeaTTaAtom, Metta.Atom.vars] using hlist es hes

/-- Specialization of the previous bridge to successful ground `simpleMatch`
results from the empty seed. This is the substitution half of the eventual
`queryEquations` witness transport: after transporting the match witness itself,
the reduct side already lines up definitionally through this theorem. -/
theorem simpleMatch_ground_apply_eq_instantiate_matchBindings
    {pattern target rhs : Atom} {mb : Bindings} {fuelMatch fuelApply : Nat} :
    GroundAtom target →
    simpleMatch pattern target Bindings.empty fuelMatch = some mb →
    atomDepth rhs + 2 ≤ fuelApply →
      toLeaTTaAtom (mb.apply rhs fuelApply) =
        Metta.instantiate (toLeaTTaMatchBindings mb) (toLeaTTaAtom rhs) := by
  intro hground hmatch hdepth
  exact toLeaTTaAtom_apply_eq_instantiate_matchBindings_of_groundBindings
    (simpleMatch_groundBindings hground hmatch)
    (simpleMatch_assignmentsNodup hmatch)
    fuelApply rhs hdepth

/-- HE-side variable renaming commutes with the structural translation once the
fuel covers the atom depth. This is the alpha-freshening boundary theorem the
equation bridge needs. -/
theorem toLeaTTaAtom_renameVars_of_depth (mapping : List (String × String)) :
    ∀ fuel a, atomDepth a + 1 ≤ fuel →
      toLeaTTaAtom (Mettapedia.Languages.MeTTa.HE.renameVars mapping a fuel) =
        Metta.renameVars mapping (toLeaTTaAtom a) := by
  intro fuel
  induction fuel with
  | zero =>
      intro a hdepth
      omega
  | succ fuel ih =>
      intro a hdepth
      cases a with
      | symbol s =>
          simp [Mettapedia.Languages.MeTTa.HE.renameVars, Metta.renameVars, toLeaTTaAtom]
      | var v =>
          simp [Mettapedia.Languages.MeTTa.HE.renameVars, Metta.renameVars, toLeaTTaAtom]
      | grounded g =>
          simp [Mettapedia.Languages.MeTTa.HE.renameVars, Metta.renameVars, toLeaTTaAtom]
      | expression es =>
          have hlist :
              ∀ es : List Atom, listDepth es + 1 ≤ fuel →
                toLeaTTaAtoms
                    (Mettapedia.Languages.MeTTa.HE.renameVars.renameVarsList mapping es fuel) =
                  (toLeaTTaAtoms es).map (Metta.renameVars mapping) := by
            intro es
            induction es with
            | nil =>
                intro _
                rfl
            | cons e es ihEs =>
                intro hes
                simp [listDepth, toLeaTTaAtoms,
                  Mettapedia.Languages.MeTTa.HE.renameVars.renameVarsList] at hes ⊢
                have hhead : atomDepth e + 1 ≤ fuel := by
                  omega
                have htail : listDepth es + 1 ≤ fuel := by
                  omega
                constructor
                · exact ih e hhead
                · exact ihEs htail
          have hes : listDepth es + 1 ≤ fuel := by
            simp [atomDepth] at hdepth
            omega
          simpa [Mettapedia.Languages.MeTTa.HE.renameVars, Metta.renameVars, toLeaTTaAtom] using
            congrArg Metta.Atom.expr (hlist es hes)

/-- The translated freshened LHS is exactly LeaTTa renaming applied to the
translated raw LHS, provided the fuel reaches the atom depth. -/
theorem toLeaTTaAtom_freshenEquation_fst
    (idx : Nat) (lhs rhs : Atom) (fuel : Nat)
    (hdepth : atomDepth lhs + 1 ≤ fuel) :
    toLeaTTaAtom (freshenEquation idx lhs rhs fuel).1 =
      Metta.renameVars
        ((freshMapping idx ((collectVars lhs fuel ++ collectVars rhs fuel).eraseDups)).1)
        (toLeaTTaAtom lhs) := by
  simp [freshenEquation]
  exact toLeaTTaAtom_renameVars_of_depth _ fuel lhs hdepth

/-- The translated freshened RHS is exactly LeaTTa renaming applied to the
translated raw RHS, provided the fuel reaches the atom depth. -/
theorem toLeaTTaAtom_freshenEquation_snd
    (idx : Nat) (lhs rhs : Atom) (fuel : Nat)
    (hdepth : atomDepth rhs + 1 ≤ fuel) :
    toLeaTTaAtom (freshenEquation idx lhs rhs fuel).2 =
      Metta.renameVars
        ((freshMapping idx ((collectVars lhs fuel ++ collectVars rhs fuel).eraseDups)).1)
        (toLeaTTaAtom rhs) := by
  simp [freshenEquation]
  exact toLeaTTaAtom_renameVars_of_depth _ fuel rhs hdepth

/-- The translated avoid-aware freshened LHS is exactly LeaTTa renaming
applied to the translated raw LHS, provided the fuel reaches the atom depth. -/
theorem toLeaTTaAtom_freshenEquationAgainst_fst
    (avoid : List String) (idx : Nat) (lhs rhs : Atom) (fuel : Nat)
    (hdepth : atomDepth lhs + 1 ≤ fuel) :
    toLeaTTaAtom (freshenEquationAgainst avoid idx lhs rhs fuel).1 =
      Metta.renameVars
        ((freshMappingAgainst idx avoid
          ((collectVars lhs fuel ++ collectVars rhs fuel).eraseDups)).1)
        (toLeaTTaAtom lhs) := by
  simp [freshenEquationAgainst]
  exact toLeaTTaAtom_renameVars_of_depth _ fuel lhs hdepth

/-- The translated avoid-aware freshened RHS is exactly LeaTTa renaming
applied to the translated raw RHS, provided the fuel reaches the atom depth. -/
theorem toLeaTTaAtom_freshenEquationAgainst_snd
    (avoid : List String) (idx : Nat) (lhs rhs : Atom) (fuel : Nat)
    (hdepth : atomDepth rhs + 1 ≤ fuel) :
    toLeaTTaAtom (freshenEquationAgainst avoid idx lhs rhs fuel).2 =
      Metta.renameVars
        ((freshMappingAgainst idx avoid
          ((collectVars lhs fuel ++ collectVars rhs fuel).eraseDups)).1)
        (toLeaTTaAtom rhs) := by
  simp [freshenEquationAgainst]
  exact toLeaTTaAtom_renameVars_of_depth _ fuel rhs hdepth

/-- HE-side model of LeaTTa's runtime freshening discipline: every variable
from the rule gets the same runtime counter suffix, matching
`Minimal.Interpreter.freshenRule`. We keep the original variable-order list
instead of deduplicating so the induced lookup order matches LeaTTa's
substitution exactly. -/
private def uniformCounterMapping (counter : Nat) (vars : List String) : List (String × String) :=
  vars.map fun v => (v, s!"{v}#{counter}")

/-- HE-side model of LeaTTa's runtime freshening on raw rules. -/
private def uniformCounterFreshenEquation (counter : Nat) (lhs rhs : Atom) (fuel : Nat) :
    Atom × Atom :=
  let vars := collectVars lhs fuel ++ collectVars rhs fuel
  let mapping := uniformCounterMapping counter vars
  (renameVars mapping lhs fuel, renameVars mapping rhs fuel)

/-- `find?` through the runtime freshening map is just `find?` on the source
variable list, decorated with the uniform counter suffix. -/
private theorem uniformCounterMapping_find?
    (counter : Nat) :
    ∀ (vars : List String) (v : String),
      (uniformCounterMapping counter vars).find? (fun p => p.1 == v) =
        (vars.find? (fun x => x == v)).map (fun x => (x, s!"{x}#{counter}")) := by
  intro vars v
  induction vars with
  | nil =>
      simp [uniformCounterMapping]
  | cons x xs ih =>
      by_cases hx : x = v
      · subst hx
        simp [uniformCounterMapping]
      · have hbeq : (x == v) = false := by
          simp [hx]
        simpa [uniformCounterMapping, hbeq] using ih

/-- LeaTTa's substitution lookup for the runtime freshening substitution is the
expected variable lookup with the uniform counter suffix. -/
private theorem uniformCounterSubst_lookup
    (counter : Nat) :
    ∀ (vars : List String) (v : String),
      Metta.Subst.lookup
          (vars.map fun x => (x, Metta.Atom.var s!"{x}#{counter}")) v =
        (vars.find? (fun x => x == v)).map (fun x => Metta.Atom.var s!"{x}#{counter}") := by
  intro vars v
  induction vars with
  | nil =>
      simp [Metta.Subst.lookup]
  | cons x xs ih =>
      by_cases hx : x = v
      · subst hx
        simp [Metta.Subst.lookup]
      · have hbeq : (x == v) = false := by
          simp [hx]
        have hne : v ≠ x := by
          intro h
          exact hx h.symm
        have hbeq' : (v == x) = false := by
          simp [hne]
        simpa [Metta.Subst.lookup, hbeq, hbeq'] using ih

/-- For the specific uniform-counter map used by LeaTTa's runtime freshening,
`renameVars` and `Subst.apply` agree exactly. This is the only shape needed to
identify `freshenRule` with translated HE freshening. -/
private theorem leaRenameVars_eq_substApply_uniformCounter
    (counter : Nat) (vars : List String) :
    ∀ a : Metta.Atom,
      Metta.renameVars (uniformCounterMapping counter vars) a =
        Metta.Subst.apply
          (vars.map fun x => (x, Metta.Atom.var s!"{x}#{counter}")) a := by
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_
  · intro s
    simp [Metta.renameVars, Metta.Subst.apply]
  · intro v
    rw [Metta.renameVars, Metta.Subst.apply,
      uniformCounterMapping_find?, uniformCounterSubst_lookup]
    cases hfind : List.find? (fun x => x == v) vars <;> simp
  · intro g
    simp [Metta.renameVars, Metta.Subst.apply]
  · intro xs ih
    simpa [Metta.renameVars, Metta.Subst.apply] using
      congrArg Metta.Atom.expr (List.map_congr_left ih)

/-- Translating the HE-side runtime-freshened LHS lands exactly on LeaTTa's
renaming surface for the same runtime counter. -/
private theorem toLeaTTaAtom_uniformCounterFreshenEquation_fst
    (counter : Nat) (lhs rhs : Atom) (fuel : Nat)
    (hdepth : atomDepth lhs + 1 ≤ fuel) :
    toLeaTTaAtom (uniformCounterFreshenEquation counter lhs rhs fuel).1 =
      Metta.renameVars
        (uniformCounterMapping counter (collectVars lhs fuel ++ collectVars rhs fuel))
        (toLeaTTaAtom lhs) := by
  simp [uniformCounterFreshenEquation]
  exact toLeaTTaAtom_renameVars_of_depth _ fuel lhs hdepth

/-- RHS companion to `toLeaTTaAtom_uniformCounterFreshenEquation_fst`. -/
private theorem toLeaTTaAtom_uniformCounterFreshenEquation_snd
    (counter : Nat) (lhs rhs : Atom) (fuel : Nat)
    (hdepth : atomDepth rhs + 1 ≤ fuel) :
    toLeaTTaAtom (uniformCounterFreshenEquation counter lhs rhs fuel).2 =
      Metta.renameVars
        (uniformCounterMapping counter (collectVars lhs fuel ++ collectVars rhs fuel))
        (toLeaTTaAtom rhs) := by
  simp [uniformCounterFreshenEquation]
  exact toLeaTTaAtom_renameVars_of_depth _ fuel rhs hdepth

/-- Exact bridge: LeaTTa's executable runtime freshening is the translation of
the corresponding HE-side `uniformCounterFreshenEquation`. This pins the
runtime-counter semantics to an HE atom pair we can reason about directly. -/
private theorem freshenRule_eq_uniformCounterFreshenEquation
    (counter : Nat) (lhs rhs : Atom) (fuel : Nat)
    (hdepthL : atomDepth lhs + 1 ≤ fuel)
    (hdepthR : atomDepth rhs + 1 ≤ fuel) :
    Metta.Minimal.freshenRule counter (toLeaTTaAtom lhs) (toLeaTTaAtom rhs) =
      (toLeaTTaAtom (uniformCounterFreshenEquation counter lhs rhs fuel).1,
        toLeaTTaAtom (uniformCounterFreshenEquation counter lhs rhs fuel).2) := by
  rw [toLeaTTaAtom_uniformCounterFreshenEquation_fst counter lhs rhs fuel hdepthL,
    toLeaTTaAtom_uniformCounterFreshenEquation_snd counter lhs rhs fuel hdepthR]
  have hvarsL :
      collectVars lhs fuel = (toLeaTTaAtom lhs).vars :=
    collectVars_eq_toLeaTTaAtom_vars_of_depth fuel lhs hdepthL
  have hvarsR :
      collectVars rhs fuel = (toLeaTTaAtom rhs).vars :=
    collectVars_eq_toLeaTTaAtom_vars_of_depth fuel rhs hdepthR
  rw [show
      uniformCounterMapping counter (collectVars lhs fuel ++ collectVars rhs fuel) =
        uniformCounterMapping counter ((toLeaTTaAtom lhs).vars ++ (toLeaTTaAtom rhs).vars) by
        simp [uniformCounterMapping, hvarsL, hvarsR]]
  unfold Metta.Minimal.freshenRule
  cases hvars : ((toLeaTTaAtom lhs).vars ++ (toLeaTTaAtom rhs).vars) with
  | nil =>
      simp [uniformCounterMapping, Metta.renameVars_nil]
  | cons v vs =>
      apply Prod.ext
      · symm
        exact leaRenameVars_eq_substApply_uniformCounter counter (v :: vs) (toLeaTTaAtom lhs)
      · symm
        exact leaRenameVars_eq_substApply_uniformCounter counter (v :: vs) (toLeaTTaAtom rhs)

private theorem mem_of_mem_zipIdx {α : Type*} {xs : List α} {x : α} {i : Nat}
    (h : (x, i) ∈ xs.zipIdx) : x ∈ xs := by
  rcases List.mem_zipIdx h with ⟨_, hi, hEq⟩
  have hi' : i < xs.length := by
    simpa using hi
  have hmem : xs[i] ∈ xs := List.getElem_mem hi'
  exact hEq.symm ▸ hmem

private theorem list_mem_split {α : Type*} {x : α} :
    ∀ {xs : List α}, x ∈ xs → ∃ pre post, xs = pre ++ x :: post := by
  intro xs hmem
  induction xs with
  | nil =>
      cases hmem
  | cons y ys ih =>
      simp at hmem
      rcases hmem with rfl | htail
      · exact ⟨[], ys, by simp⟩
      · rcases ih htail with ⟨pre, post, hsplit⟩
        exact ⟨y :: pre, post, by simp [hsplit]⟩

/-- Ground HE atoms contain no variables, so the query-side freshening pass
sees an empty variable list regardless of fuel. -/
private theorem groundAtom_collectVars_eq_nil :
    ∀ {a : Atom}, GroundAtom a → ∀ fuel, collectVars a fuel = [] := by
  intro a hground
  induction hground with
  | symbol s =>
      intro fuel
      cases fuel <;> simp [collectVars]
  | grounded g =>
      intro fuel
      cases fuel <;> simp [collectVars]
  | @expression es hElems ih =>
      intro fuel
      cases fuel with
      | zero =>
          simp [collectVars]
      | succ n =>
          have hlist :
              ∀ es : List Atom, (∀ e ∈ es, collectVars e n = []) →
                collectVars.collectVarsList es n = [] := by
            intro es
            induction es with
            | nil =>
                intro _
                simp [collectVars.collectVarsList]
            | cons e es ihEs =>
                intro hEs
                have hhead : collectVars e n = [] := hEs e (by simp)
                have htail : ∀ e' ∈ es, collectVars e' n = [] := by
                  intro e' he'
                  exact hEs e' (by simp [he'])
                simp [collectVars.collectVarsList, hhead, ihEs htail]
          have hElemsNil : ∀ e ∈ es, collectVars e n = [] := by
            intro e he
            exact ih e he n
          simp [collectVars, hlist _ hElemsNil]

/-- Renaming by the empty map is the identity on HE atoms. -/
private theorem renameVars_nil :
    ∀ fuel a, renameVars [] a fuel = a := by
  intro fuel
  induction fuel with
  | zero =>
      intro a
      simp [renameVars]
  | succ fuel ih =>
      intro a
      cases a with
      | symbol s =>
          simp [renameVars]
      | var v =>
          simp [renameVars]
      | grounded g =>
          simp [renameVars]
      | expression es =>
          have hlist :
              ∀ es : List Atom, renameVars.renameVarsList [] es fuel = es := by
            intro es
            induction es with
            | nil =>
                simp [renameVars.renameVarsList]
            | cons e es ihEs =>
                simp [renameVars.renameVarsList, ih e, ihEs]
          simp [renameVars, hlist]

/-- Translating a ground HE atom yields a LeaTTa atom with no free variables. -/
theorem toLeaTTaAtom_vars_nil_of_ground :
    ∀ {a : Atom}, GroundAtom a → (toLeaTTaAtom a).vars = [] := by
  intro a hground
  induction hground with
  | symbol s =>
      simp [toLeaTTaAtom, Metta.Atom.vars]
  | grounded g =>
      simp [toLeaTTaAtom, Metta.Atom.vars]
  | @expression es hElems ih =>
      have hlist : ∀ es : List Atom, (∀ e ∈ es, (toLeaTTaAtom e).vars = []) →
          ((toLeaTTaAtoms es).map Metta.Atom.vars).flatten = [] := by
        intro es
        induction es with
        | nil =>
            simp [toLeaTTaAtoms]
        | cons e es ihEs =>
            intro hEs
            have hhead : (toLeaTTaAtom e).vars = [] := hEs e (by simp)
            have htail : ∀ e' ∈ es, (toLeaTTaAtom e').vars = [] := by
              intro e' he'
              exact hEs e' (by simp [he'])
            simp [toLeaTTaAtoms, hhead, ihEs htail]
      have hElemsNil : ∀ e ∈ es, (toLeaTTaAtom e).vars = [] := by
        intro e he
        exact ih e he
      simpa [toLeaTTaAtom, Metta.Atom.vars] using hlist es hElemsNil

/-- A fully ground equation is unchanged by HE's local freshening pass. -/
private theorem freshenEquation_eq_of_ground
    (idx : Nat) {lhs rhs : Atom}
    (hLhsGround : GroundAtom lhs) (hRhsGround : GroundAtom rhs)
    (fuel : Nat) :
    freshenEquation idx lhs rhs fuel = (lhs, rhs) := by
  have hvarsL : collectVars lhs fuel = [] :=
    groundAtom_collectVars_eq_nil hLhsGround fuel
  have hvarsR : collectVars rhs fuel = [] :=
    groundAtom_collectVars_eq_nil hRhsGround fuel
  simp [freshenEquation, hvarsL, hvarsR, freshMapping, renameVars_nil]

/-- A fully ground equation is also unchanged by the visible-avoid freshening
pass, regardless of the caller's avoid set. -/
private theorem freshenEquationAgainst_eq_of_ground
    (avoid : List String) (idx : Nat) {lhs rhs : Atom}
    (hLhsGround : GroundAtom lhs) (hRhsGround : GroundAtom rhs)
    (fuel : Nat) :
    freshenEquationAgainst avoid idx lhs rhs fuel = (lhs, rhs) := by
  have hvarsL : collectVars lhs fuel = [] :=
    groundAtom_collectVars_eq_nil hLhsGround fuel
  have hvarsR : collectVars rhs fuel = [] :=
    groundAtom_collectVars_eq_nil hRhsGround fuel
  simp [freshenEquationAgainst, hvarsL, hvarsR, freshMappingAgainst, renameVars_nil]

/-- Safe compatibility fragment: in a singleton space containing a fully ground
equation, the repaired visible-avoid query surface coincides with the ordinary
faithful HE query surface.  The proof is not about all queries; it uses that
the rule itself has no equation-local variables to freshen. -/
theorem queryEquationsAgainstVisible_single_ground_rule_eq_queryEquations
    {lhs rhs atom : Atom} (hLhsGround : GroundAtom lhs)
    (hRhsGround : GroundAtom rhs) (fuel : Nat) :
    queryEquationsAgainstVisible
        (Space.ofList [.expression [.symbol "=", lhs, rhs]]) atom fuel =
      queryEquations
        (Space.ofList [.expression [.symbol "=", lhs, rhs]]) atom fuel := by
  cases fuel with
  | zero =>
      simp [queryEquationsAgainstVisible, queryEquations]
  | succ n =>
      have hagainst :
          freshenEquationAgainst ((collectVars atom (n + 1)).eraseDups)
              0 lhs rhs (n + 1) = (lhs, rhs) :=
        freshenEquationAgainst_eq_of_ground
          ((collectVars atom (n + 1)).eraseDups) 0 hLhsGround hRhsGround (n + 1)
      have hordinary :
          freshenEquation 0 lhs rhs (n + 1) = (lhs, rhs) :=
        freshenEquation_eq_of_ground 0 hLhsGround hRhsGround (n + 1)
      simp [queryEquationsAgainstVisible, queryEquations, Space.ofList,
        hagainst, hordinary]

/-- Membership transport for the singleton ground-rule compatibility fragment. -/
theorem queryEquationsAgainstVisible_single_ground_rule_mem_queryEquations
    {lhs rhs atom out : Atom} {qb : Bindings} {fuel : Nat}
    (hLhsGround : GroundAtom lhs) (hRhsGround : GroundAtom rhs)
    (hmem : (out, qb) ∈
      queryEquationsAgainstVisible
        (Space.ofList [.expression [.symbol "=", lhs, rhs]]) atom fuel) :
    (out, qb) ∈
      queryEquations
        (Space.ofList [.expression [.symbol "=", lhs, rhs]]) atom fuel := by
  simpa [queryEquationsAgainstVisible_single_ground_rule_eq_queryEquations
      hLhsGround hRhsGround fuel] using hmem

/-- Exact empty-seed bridge on the ground-pattern fragment: successful HE
matching against a ground pattern leaves the empty seed unchanged and lands the
empty LeaTTa binding witness on the direct matcher surface. This is the exact
closed-rule fragment used by the positive equation-step theorem below. -/
private theorem simpleMatch_ground_empty_exact :
    ∀ fuel,
      (∀ {pattern target qb},
        GroundAtom pattern →
        simpleMatch pattern target Bindings.empty fuel = some qb →
          qb = Bindings.empty ∧
          Metta.Bindings.empty ∈
            Metta.matchAtoms (toLeaTTaAtom pattern) (toLeaTTaAtom target)) ∧
      (∀ {ps ts qb},
        (∀ p ∈ ps, GroundAtom p) →
        simpleMatch.simpleMatchList ps ts Bindings.empty fuel = some qb →
          qb = Bindings.empty ∧
          Metta.Bindings.empty ∈
            Metta.matchAll none [Metta.Bindings.empty] (toLeaTTaAtoms ps) (toLeaTTaAtoms ts)) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro pattern target qb _ hmatch
        simp [simpleMatch] at hmatch
      · intro ps ts qb hground hmatch
        cases ps with
        | nil =>
            cases ts with
            | nil =>
                simp [simpleMatch.simpleMatchList] at hmatch
                subst hmatch
                simp [Metta.matchAll]
            | cons t ts =>
                simp [simpleMatch.simpleMatchList] at hmatch
        | cons p ps =>
            cases ts with
            | nil =>
                simp [simpleMatch.simpleMatchList] at hmatch
            | cons t ts =>
                simp [simpleMatch.simpleMatchList, simpleMatch] at hmatch
  | succ fuel ih =>
      obtain ⟨ihAtom, ihList⟩ := ih
      have hAtomSucc :
          ∀ {pattern target qb},
            GroundAtom pattern →
            simpleMatch pattern target Bindings.empty (Nat.succ fuel) = some qb →
              qb = Bindings.empty ∧
              Metta.Bindings.empty ∈
                Metta.matchAtoms (toLeaTTaAtom pattern) (toLeaTTaAtom target) := by
        intro pattern target qb hground hmatch
        cases hground with
        | symbol s =>
            cases target with
            | symbol t =>
                by_cases hst : s = t
                · subst hst
                  simp [simpleMatch] at hmatch
                  subst qb
                  exact ⟨rfl, by simp [Metta.Bindings.empty, Metta.matchAtoms,
                    Metta.matchAtomsWith, Metta.Bindings.hasLoop,
                    Metta.Bindings.vars, toLeaTTaAtom]⟩
                · simp [simpleMatch, hst] at hmatch
            | var v =>
                simp [simpleMatch] at hmatch
            | grounded g =>
                simp [simpleMatch] at hmatch
            | expression es =>
                simp [simpleMatch] at hmatch
        | grounded g =>
            cases target with
            | grounded h =>
                by_cases hgh : g = h
                · subst hgh
                  simp [simpleMatch] at hmatch
                  subst qb
                  refine ⟨rfl, ?_⟩
                  simpa [Metta.Bindings.empty, Metta.matchAtoms, Metta.matchAtomsWith,
                    Metta.Bindings.hasLoop, Metta.Bindings.vars, toLeaTTaAtom] using
                    toLeaTTaAtom_grounded_equiv_self g
                · simp [simpleMatch, hgh] at hmatch
            | var v =>
                simp [simpleMatch] at hmatch
            | symbol s =>
                simp [simpleMatch] at hmatch
            | expression es =>
                simp [simpleMatch] at hmatch
        | @expression ps hElems =>
            cases target with
            | expression ts =>
                by_cases hlen : ps.length != ts.length
                · simp [simpleMatch, hlen] at hmatch
                · have hps : ∀ p ∈ ps, GroundAtom p := by
                    simpa using hElems
                  have hlist :
                      simpleMatch.simpleMatchList ps ts Bindings.empty fuel = some qb := by
                    simpa [simpleMatch, hlen] using hmatch
                  obtain ⟨hqb, hmem⟩ := ihList hps hlist
                  subst hqb
                  refine ⟨rfl, ?_⟩
                  simpa [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom,
                    hlen, Metta.Bindings.empty, Metta.Bindings.hasLoop,
                    Metta.Bindings.vars] using hmem
            | var v =>
                simp [simpleMatch] at hmatch
            | symbol s =>
                simp [simpleMatch] at hmatch
            | grounded g =>
                simp [simpleMatch] at hmatch
      have hListSucc :
          ∀ {ps ts qb},
            (∀ p ∈ ps, GroundAtom p) →
            simpleMatch.simpleMatchList ps ts Bindings.empty (Nat.succ fuel) = some qb →
              qb = Bindings.empty ∧
              Metta.Bindings.empty ∈
                Metta.matchAll none [Metta.Bindings.empty] (toLeaTTaAtoms ps) (toLeaTTaAtoms ts) := by
        intro ps
        induction ps with
        | nil =>
            intro ts qb hground hmatch
            cases ts with
            | nil =>
                simp [simpleMatch.simpleMatchList] at hmatch
                subst hmatch
                simp [Metta.matchAll]
            | cons t ts =>
                simp [simpleMatch.simpleMatchList] at hmatch
        | cons p ps ihPs =>
            intro ts qb hground hmatch
            cases ts with
            | nil =>
                simp [simpleMatch.simpleMatchList] at hmatch
            | cons t ts =>
                unfold simpleMatch.simpleMatchList at hmatch
                have hpGround : GroundAtom p := hground p (by simp)
                have hpsGround : ∀ p' ∈ ps, GroundAtom p' := by
                  intro p' hp'
                  exact hground p' (by simp [hp'])
                cases hhd : simpleMatch p t Bindings.empty (Nat.succ fuel) with
                | none =>
                    rw [hhd] at hmatch
                    simp at hmatch
                | some b' =>
                    rw [hhd] at hmatch
                    simp at hmatch
                    obtain ⟨hb', hhead⟩ := hAtomSucc hpGround hhd
                    subst hb'
                    obtain ⟨hqb, htail⟩ := ihPs hpsGround hmatch
                    subst hqb
                    have hmergeEmpty :
                        Metta.Bindings.empty ∈
                          Metta.Bindings.merge Metta.Bindings.empty Metta.Bindings.empty := by
                      simp [Metta.Bindings.empty, merge_empty_right]
                    have hheadSeeded :
                        Metta.Bindings.empty ∈
                          (Metta.matchAtoms (toLeaTTaAtom p) (toLeaTTaAtom t)).flatMap
                            (fun mb => Metta.Bindings.merge Metta.Bindings.empty mb) := by
                      exact List.mem_flatMap.mpr ⟨Metta.Bindings.empty, hhead, hmergeEmpty⟩
                    refine ⟨rfl, ?_⟩
                    exact matchAll_cons_of_head_tail hheadSeeded htail
      exact ⟨hAtomSucc, hListSucc⟩

/-- Faithful post-G3 query witness: the public equation-query surface now
matches the queried atom against the freshened rule LHS with `matchAtoms`,
merges the result with the empty ambient bindings, and filters loops. The old
`simpleMatch = some qb` shape is valid only on staged fragments. -/
def FaithfulQueryWitness (atom lhs' : Atom) (qb : Bindings) (fuel : Nat) : Prop :=
  ∃ mb,
    mb ∈ matchAtoms atom lhs' fuel ∧
    qb ∈ mergeBindings mb Bindings.empty fuel ∧
    qb.hasLoop = false

/-- In a faithful query witness the final public query binding is exactly the
raw matcher binding: the query path only merges the matcher result with the
empty ambient binding set before filtering loops. -/
theorem faithfulQueryWitness_matchBinding_eq
    {atom lhs' : Atom} {qb : Bindings} {fuel : Nat}
    (h : FaithfulQueryWitness atom lhs' qb fuel) :
    ∃ mb, mb ∈ matchAtoms atom lhs' fuel ∧ qb = mb ∧ qb.hasLoop = false := by
  rcases h with ⟨mb, hmb, hmerge, hloop⟩
  cases fuel with
  | zero =>
      simp [mergeBindings] at hmerge
  | succ n =>
      have hqb : qb = mb := by
        rw [mergeBindings_empty_right mb n] at hmerge
        simpa using hmerge
      exact ⟨mb, hmb, hqb, hloop⟩

/-- The final binding of a faithful query witness is itself one of the official
HE `matchAtoms` outputs. -/
theorem faithfulQueryWitness_matchAtoms_mem
    {atom lhs' : Atom} {qb : Bindings} {fuel : Nat}
    (h : FaithfulQueryWitness atom lhs' qb fuel) :
    qb ∈ matchAtoms atom lhs' fuel := by
  obtain ⟨mb, hmb, hqb, _hloop⟩ := faithfulQueryWitness_matchBinding_eq h
  simpa [hqb] using hmb

/-- Faithful query witnesses inherit the HE matcher's equality-aware invariant:
variable-variable matches are represented by equalities, not by variable-valued
assignments. -/
theorem faithfulQueryWitness_noVarAssignmentValues
    {atom lhs' : Atom} {qb : Bindings} {fuel : Nat}
    (h : FaithfulQueryWitness atom lhs' qb fuel) :
    NoVarAssignmentValues qb :=
  DeclMatchSpec.matchAtoms_noVarAssignmentValues
    (faithfulQueryWitness_matchAtoms_mem h)

/-- Faithful query witnesses also inherit HE's assignment-key uniqueness
invariant from the official matcher. -/
theorem faithfulQueryWitness_assignmentsNodup
    {atom lhs' : Atom} {qb : Bindings} {fuel : Nat}
    (h : FaithfulQueryWitness atom lhs' qb fuel) :
    AssignmentsNodup qb :=
  DeclMatchSpec.matchAtoms_assignmentsNodup
    (faithfulQueryWitness_matchAtoms_mem h)

/-- A `queryEquations` witness comes from a specific indexed raw equation in the
space together with its freshened matcher witness. This is the precise bridge
entry point for transporting HE query evidence into LeaTTa. -/
theorem mem_queryEquations_decompose
    {space : Space} {atom rhs : Atom} {qb : Bindings} {fuel : Nat}
    (hmem : (rhs, qb) ∈ queryEquations space atom fuel) :
    ∃ eqidx ∈ space.atoms.zipIdx, ∃ lhs rawRhs,
      eqidx.1 = .expression [.symbol "=", lhs, rawRhs] ∧
      (freshenEquation eqidx.2 lhs rawRhs fuel).2 = rhs ∧
      FaithfulQueryWitness atom (freshenEquation eqidx.2 lhs rawRhs fuel).1 qb fuel := by
  cases fuel with
  | zero =>
      simp [queryEquations] at hmem
  | succ n =>
      rcases List.mem_flatMap.mp hmem with ⟨eqidx, heqidx, hout⟩
      rcases eqidx with ⟨eq, idx⟩
      cases eq with
      | symbol s =>
          simp at hout
      | var v =>
          simp at hout
      | grounded g =>
          simp at hout
      | expression es =>
          cases es with
          | nil =>
              simp at hout
          | cons hd tl =>
              cases hd with
              | symbol s =>
                  by_cases hs : s = "="
                  · subst hs
                    cases tl with
                    | nil =>
                        simp at hout
                    | cons lhs tl1 =>
                        cases tl1 with
                        | nil =>
                            simp at hout
                        | cons rawRhs tl2 =>
                            cases tl2 with
                            | nil =>
                                rcases List.mem_flatMap.mp hout with ⟨mb, hmb, hfiltered⟩
                                rcases List.mem_filterMap.mp hfiltered with ⟨merged, hmerge, hout'⟩
                                by_cases hloop : merged.hasLoop
                                · simp [hloop] at hout'
                                · simp [hloop] at hout'
                                  rcases hout' with ⟨hRhs, hQb⟩
                                  refine
                                    ⟨(Atom.expression [Atom.symbol "=", lhs, rawRhs], idx), heqidx,
                                      lhs, rawRhs, rfl, hRhs, ?_⟩
                                  subst hQb
                                  exact ⟨mb, hmb, hmerge, by simpa using (Bool.eq_false_iff.mpr hloop)⟩
                            | cons extra tl3 =>
                                simp at hout
                  · simp [hs] at hout
              | var v =>
                  simp at hout
              | grounded g =>
                  simp at hout
              | expression es' =>
                  simp at hout

/-- The visible-avoid query surface has the same raw-rule decomposition shape
as `queryEquations`: every witness still comes from a specific indexed raw
equation together with its avoid-aware freshened matcher witness. This lets the
bridge reuse the same candidate-transport architecture once it pivots to the
stronger freshness discipline. -/
theorem mem_queryEquationsAgainstVisible_decompose
    {space : Space} {atom rhs : Atom} {qb : Bindings} {fuel : Nat}
    (hmem : (rhs, qb) ∈ queryEquationsAgainstVisible space atom fuel) :
    ∃ eqidx ∈ space.atoms.zipIdx, ∃ lhs rawRhs,
      eqidx.1 = .expression [.symbol "=", lhs, rawRhs] ∧
      (freshenEquationAgainst ((collectVars atom fuel).eraseDups) eqidx.2 lhs rawRhs fuel).2 = rhs ∧
      FaithfulQueryWitness atom
        (freshenEquationAgainst ((collectVars atom fuel).eraseDups) eqidx.2 lhs rawRhs fuel).1
        qb fuel := by
  cases fuel with
  | zero =>
      simp [queryEquationsAgainstVisible] at hmem
  | succ n =>
      rcases List.mem_flatMap.mp hmem with ⟨eqidx, heqidx, hout⟩
      rcases eqidx with ⟨eq, idx⟩
      cases eq with
      | symbol s =>
          simp at hout
      | var v =>
          simp at hout
      | grounded g =>
          simp at hout
      | expression es =>
          cases es with
          | nil =>
              simp at hout
          | cons hd tl =>
              cases hd with
              | symbol s =>
                  by_cases hs : s = "="
                  · subst hs
                    cases tl with
                    | nil =>
                        simp at hout
                    | cons lhs tl1 =>
                        cases tl1 with
                        | nil =>
                            simp at hout
                        | cons rawRhs tl2 =>
                            cases tl2 with
                            | nil =>
                                rcases List.mem_flatMap.mp hout with ⟨mb, hmb, hfiltered⟩
                                rcases List.mem_filterMap.mp hfiltered with ⟨merged, hmerge, hout'⟩
                                by_cases hloop : merged.hasLoop
                                · simp [hloop] at hout'
                                · simp [hloop] at hout'
                                  rcases hout' with ⟨hRhs, hQb⟩
                                  refine
                                    ⟨(Atom.expression [Atom.symbol "=", lhs, rawRhs], idx), heqidx,
                                      lhs, rawRhs, rfl, hRhs, ?_⟩
                                  subst hQb
                                  exact ⟨mb, hmb, hmerge, by simpa using (Bool.eq_false_iff.mpr hloop)⟩
                            | cons extra tl3 =>
                                simp at hout
                  · simp [hs] at hout
              | var v =>
                  simp at hout
              | grounded g =>
                  simp at hout
              | expression es' =>
                  simp at hout

/-- The translation preserves the head key used by LeaTTa's first-argument
indexing layer. -/
@[simp] theorem headKey_toLeaTTaAtom (a : Atom) :
    Metta.Minimal.headKey (toLeaTTaAtom a) = heHeadKey a := by
  cases a with
  | symbol s =>
      rfl
  | var v =>
      rfl
  | grounded g =>
      rfl
  | expression es =>
      cases es with
      | nil =>
          rfl
      | cons h tail =>
          cases h with
          | symbol s =>
              rfl
          | var v =>
              rfl
          | grounded g =>
              rfl
          | expression inner =>
              rfl

/-- Equation-local HE freshening preserves the structural head key of the LHS. -/
private theorem heHeadKey_freshenEquation_fst
    (idx : Nat) (lhs rhs : Atom) (fuel : Nat) :
    heHeadKey (freshenEquation idx lhs rhs fuel).1 = heHeadKey lhs := by
  cases fuel with
  | zero =>
      cases lhs <;> simp [freshenEquation, renameVars, heHeadKey, freshMapping]
  | succ n =>
      cases lhs with
      | symbol s =>
          simp [freshenEquation, renameVars, heHeadKey, freshMapping]
      | var v =>
          simp [freshenEquation, renameVars, heHeadKey, freshMapping]
      | grounded g =>
          simp [freshenEquation, renameVars, heHeadKey, freshMapping]
      | expression es =>
          cases es with
          | nil =>
              simp [freshenEquation, renameVars, heHeadKey, freshMapping,
                renameVars.renameVarsList]
          | cons hd tl =>
              cases hd with
              | symbol s =>
                  cases n <;> rfl
              | var v =>
                  cases n <;> rfl
              | grounded g =>
                  cases n <;> rfl
              | expression inner =>
                  cases n <;> rfl

/-- The visible-avoid HE freshening surface also preserves the structural head
key of the LHS. Avoiding visible names may change fresh suffix choices, but it
never changes the rule head that candidate indexing sees. -/
private theorem heHeadKey_freshenEquationAgainst_fst
    (avoid : List String) (idx : Nat) (lhs rhs : Atom) (fuel : Nat) :
    heHeadKey (freshenEquationAgainst avoid idx lhs rhs fuel).1 = heHeadKey lhs := by
  cases fuel with
  | zero =>
      cases lhs <;> simp [freshenEquationAgainst, renameVars, heHeadKey,
        freshMappingAgainst, chooseFreshName]
  | succ n =>
      cases lhs with
      | symbol s =>
          simp [freshenEquationAgainst, renameVars, heHeadKey, freshMappingAgainst,
            chooseFreshName]
      | var v =>
          simp [freshenEquationAgainst, renameVars, heHeadKey, freshMappingAgainst,
            chooseFreshName]
      | grounded g =>
          simp [freshenEquationAgainst, renameVars, heHeadKey, freshMappingAgainst,
            chooseFreshName]
      | expression es =>
          cases es with
          | nil =>
              simp [freshenEquationAgainst, renameVars, heHeadKey, freshMappingAgainst,
                chooseFreshName, renameVars.renameVarsList]
          | cons hd tl =>
              cases hd with
              | symbol s =>
                  cases n <;> rfl
              | var v =>
                  cases n <;> rfl
              | grounded g =>
                  cases n <;> rfl
              | expression inner =>
                  cases n <;> rfl

/-- Successful symbol/symbol HE matching forces the literal head symbols to
agree, and does not change the binding state. -/
private theorem simpleMatch_symbol_success
    {s t : String} {b qb : Bindings} {fuel : Nat}
    (hmatch : simpleMatch (.symbol s) (.symbol t) b fuel = some qb) :
    s = t ∧ qb = b := by
  cases fuel with
  | zero =>
      simp [simpleMatch] at hmatch
  | succ n =>
      by_cases hst : s = t
      · subst hst
        simp [simpleMatch] at hmatch
        exact ⟨rfl, hmatch.symm⟩
      · simp [simpleMatch, hst] at hmatch

/-- Successful HE matching against a symbol-headed query can only come from a
symbol-headed pattern with the same head symbol, or from a head-less pattern. -/
private theorem simpleMatch_headKey_compat :
    ∀ {fuel pattern target b qb k},
      simpleMatch pattern target b fuel = some qb →
      heHeadKey target = some k →
      heHeadKey pattern = some k ∨ heHeadKey pattern = none := by
  intro fuel
  cases fuel with
  | zero =>
      intro pattern target b qb k hmatch
      simp [simpleMatch] at hmatch
  | succ n =>
      intro pattern target b qb k hmatch htarget
      cases pattern with
      | var v =>
          exact Or.inr rfl
      | symbol s =>
          cases target with
          | symbol t =>
              simp [simpleMatch] at hmatch
              by_cases hst : s = t
              · subst hst
                simp [heHeadKey] at htarget
                subst htarget
                exact Or.inl rfl
              · simp [hst] at hmatch
          | var v =>
              simp [heHeadKey] at htarget
          | grounded g =>
              simp [heHeadKey] at htarget
          | expression es =>
              cases es with
              | nil =>
                  simp [heHeadKey] at htarget
              | cons hd tl =>
                  cases hd with
                  | symbol t =>
                      simp [simpleMatch] at hmatch
                  | var v =>
                      simp [heHeadKey] at htarget
                  | grounded g =>
                      simp [heHeadKey] at htarget
                  | expression inner =>
                      simp [heHeadKey] at htarget
      | grounded g =>
          cases target <;> simp [simpleMatch, heHeadKey] at hmatch htarget
      | expression ps =>
          cases target with
          | symbol s =>
              simp [simpleMatch] at hmatch htarget
          | var v =>
              simp [simpleMatch] at hmatch htarget
          | grounded g =>
              simp [simpleMatch] at hmatch htarget
          | expression ts =>
              cases ps with
              | nil =>
                  exact Or.inr rfl
              | cons p ps' =>
                  cases ts with
                  | nil =>
                      simp [heHeadKey] at htarget
                  | cons t ts' =>
                      cases p with
                      | symbol s =>
                          cases t with
                          | symbol tname =>
                              have hlist :
                                  simpleMatch.simpleMatchList
                                      (Atom.symbol s :: ps') (Atom.symbol tname :: ts') b n = some qb := by
                                have htail :
                                      ps'.length = ts'.length ∧
                                        simpleMatch.simpleMatchList
                                          (Atom.symbol s :: ps') (Atom.symbol tname :: ts') b n = some qb := by
                                      simpa [simpleMatch] using hmatch
                                exact htail.2
                              unfold simpleMatch.simpleMatchList at hlist
                              cases hhd : simpleMatch (.symbol s) (.symbol tname) b n with
                              | none =>
                                  simp [hhd] at hlist
                              | some b' =>
                                  simp [hhd] at hlist
                                  have hs : s = tname := (simpleMatch_symbol_success hhd).1
                                  have hkname : tname = k := by
                                    simpa [heHeadKey] using htarget
                                  subst hs
                                  subst hkname
                                  exact Or.inl rfl
                          | var v =>
                              simp [heHeadKey] at htarget
                          | grounded g =>
                              simp [heHeadKey] at htarget
                          | expression inner =>
                              simp [heHeadKey] at htarget
                      | var v =>
                          exact Or.inr rfl
                      | grounded g =>
                          exact Or.inr rfl
                      | expression inner =>
                          exact Or.inr rfl

private theorem matchListAccRel_headKey_compat
    {targets patterns : List Atom} {seed out : Bindings} {k : String}
    (h : DeclMatchSpec.MatchListAccRel targets patterns seed out)
    (htarget : heHeadKey (.expression targets) = some k) :
    heHeadKey (.expression patterns) = some k ∨
      heHeadKey (.expression patterns) = none := by
  cases targets with
  | nil =>
      cases h
      simp [heHeadKey] at htarget
  | cons t ts =>
      cases patterns with
      | nil =>
          cases h
      | cons p ps =>
          cases h with
          | cons hHead _hTail =>
              cases t with
              | symbol s =>
                  have hsk : s = k := by
                    simpa [heHeadKey] using htarget
                  cases hHead with
                  | symSym =>
                      subst hsk
                      exact Or.inl rfl
                  | nonVarVar hnv =>
                      exact Or.inr rfl
              | var v =>
                  simp [heHeadKey] at htarget
              | grounded g =>
                  simp [heHeadKey] at htarget
              | expression es =>
                  simp [heHeadKey] at htarget

private theorem matchRel_headKey_compat
    {target pattern : Atom} {b : Bindings} {k : String}
    (h : DeclMatchSpec.MatchRel target pattern b)
    (htarget : heHeadKey target = some k) :
    heHeadKey pattern = some k ∨ heHeadKey pattern = none := by
  cases h with
  | symSym s =>
      have hsk : s = k := by
        simpa [heHeadKey] using htarget
      subst hsk
      exact Or.inl rfl
  | varVar a b =>
      simp [heHeadKey] at htarget
  | varNonVar hnv =>
      simp [heHeadKey] at htarget
  | nonVarVar hnv =>
      exact Or.inr rfl
  | grounded g =>
      simp [heHeadKey] at htarget
  | expr hlist =>
      exact matchListAccRel_headKey_compat hlist htarget

private theorem faithfulQueryWitness_headKey_compat
    {atom lhs' : Atom} {qb : Bindings} {fuel : Nat} {k : String}
    (h : FaithfulQueryWitness atom lhs' qb fuel)
    (hatom : heHeadKey atom = some k) :
    heHeadKey lhs' = some k ∨ heHeadKey lhs' = none := by
  rcases h with ⟨mb, hmb, _hmerge, _hloop⟩
  exact matchRel_headKey_compat (DeclMatchSpec.matchAtoms_sound hmb) hatom

/-- The translated `(= lhs rhs)` rules present in an HE atom list. This helper
matches the exact rule surface consumed by both LeaTTa `Space.equalityRules`
and LeaTTa's indexed-kernel `extractRules`. -/
def translatedEquationRules : List Atom → List (Metta.Atom × Metta.Atom)
  | [] => []
  | atom :: rest =>
      match atom with
      | .expression (.symbol s :: tail) =>
          if s = "=" then
            match tail with
            | [lhs, rhs] =>
                (toLeaTTaAtom lhs, toLeaTTaAtom rhs) :: translatedEquationRules rest
            | _ => translatedEquationRules rest
          else
            translatedEquationRules rest
      | _ => translatedEquationRules rest

/-- Translating an HE atom list preserves exactly the LeaTTa `equalityRules`
surface. -/
@[simp] theorem equalityRules_toLeaTTaAtoms (atoms : List Atom) :
    (Metta.Space.equalityRules ⟨toLeaTTaAtoms atoms⟩) = translatedEquationRules atoms := by
  induction atoms with
  | nil =>
      rfl
  | cons a atoms ih =>
      cases a with
      | symbol s =>
          simpa [translatedEquationRules, toLeaTTaAtom, toLeaTTaAtoms, Metta.Space.equalityRules, List.filterMap] using ih
      | var v =>
          simpa [translatedEquationRules, toLeaTTaAtom, toLeaTTaAtoms, Metta.Space.equalityRules, List.filterMap] using ih
      | grounded g =>
          simpa [translatedEquationRules, toLeaTTaGround, toLeaTTaAtom, toLeaTTaAtoms, Metta.Space.equalityRules, List.filterMap] using ih
      | expression es =>
          cases es with
          | nil =>
              simpa [translatedEquationRules, toLeaTTaAtom, toLeaTTaAtoms, Metta.Space.equalityRules, List.filterMap] using ih
          | cons h tail =>
              cases h with
              | symbol s =>
                  by_cases hs : s = "="
                  · subst hs
                    cases tail with
                    | nil =>
                        simpa [translatedEquationRules, toLeaTTaAtom, toLeaTTaAtoms, Metta.Space.equalityRules, List.filterMap] using ih
                    | cons a1 tail1 =>
                        cases tail1 with
                        | nil =>
                            simpa [translatedEquationRules, toLeaTTaAtom, toLeaTTaAtoms, Metta.Space.equalityRules, List.filterMap] using ih
                        | cons a2 tail2 =>
                            cases tail2 with
                            | nil =>
                                simpa [translatedEquationRules, toLeaTTaAtom, toLeaTTaAtoms, Metta.Space.equalityRules, List.filterMap] using
                                  congrArg (List.cons (toLeaTTaAtom a1, toLeaTTaAtom a2)) ih
                            | cons a3 tail3 =>
                                simpa [translatedEquationRules, toLeaTTaAtom, toLeaTTaAtoms, Metta.Space.equalityRules, List.filterMap] using ih
                  · simpa [translatedEquationRules, toLeaTTaAtom, toLeaTTaAtoms, Metta.Space.equalityRules, List.filterMap, hs] using ih
              | var v =>
                  simpa [translatedEquationRules, toLeaTTaAtom, toLeaTTaAtoms, Metta.Space.equalityRules, List.filterMap] using ih
              | grounded g =>
                  simpa [translatedEquationRules, toLeaTTaGround, toLeaTTaAtom, toLeaTTaAtoms, Metta.Space.equalityRules, List.filterMap] using ih
              | expression inner =>
                  simpa [translatedEquationRules, toLeaTTaAtom, toLeaTTaAtoms, Metta.Space.equalityRules, List.filterMap] using ih

/-- Translating an HE space preserves exactly the equation rules visible to
LeaTTa's executable space layer. -/
@[simp] theorem equalityRules_toLeaTTaSpace (space : Space) :
    (toLeaTTaSpace space).equalityRules = translatedEquationRules space.atoms := by
  exact equalityRules_toLeaTTaAtoms space.atoms

/-- LeaTTa's index-layer rule extraction sees the same translated equation
surface as `Space.equalityRules`. This is the raw rule-space identity needed
before we can compare step relations. -/
@[simp] theorem extractRules_toLeaTTaAtoms (atoms : List Atom) :
    Metta.Minimal.extractRules (toLeaTTaAtoms atoms) = translatedEquationRules atoms := by
  exact equalityRules_toLeaTTaAtoms atoms

/-- The two LeaTTa views of translated HE equations coincide definitionally:
plain-space `equalityRules` and the kernel's `extractRules` see the same rule
list. -/
@[simp] theorem extractRules_eq_equalityRules (space : Space) :
    Metta.Minimal.extractRules (toLeaTTaSpace space).atoms =
      (toLeaTTaSpace space).equalityRules := by
  exact (extractRules_toLeaTTaAtoms space.atoms).trans
    (equalityRules_toLeaTTaSpace space).symm

private theorem mem_translatedEquationRules_of_mem_eq_atom
    {atoms : List Atom} {lhs rhs : Atom}
    (hmem : Atom.expression [Atom.symbol "=", lhs, rhs] ∈ atoms) :
    (toLeaTTaAtom lhs, toLeaTTaAtom rhs) ∈ translatedEquationRules atoms := by
  rw [← equalityRules_toLeaTTaAtoms atoms]
  unfold Metta.Space.equalityRules
  refine List.mem_filterMap.mpr ?_
  refine ⟨toLeaTTaAtom (.expression [.symbol "=", lhs, rhs]), ?_, ?_⟩
  · simpa [toLeaTTaAtom] using mem_toLeaTTaAtoms_of_mem hmem
  · simp [toLeaTTaAtom]

private theorem mem_extractRules_of_mem_eq_atom
    {atoms : List Atom} {lhs rhs : Atom}
    (hmem : Atom.expression [Atom.symbol "=", lhs, rhs] ∈ atoms) :
    (toLeaTTaAtom lhs, toLeaTTaAtom rhs) ∈ Metta.Minimal.extractRules (toLeaTTaAtoms atoms) := by
  simpa using
    (mem_translatedEquationRules_of_mem_eq_atom (atoms := atoms) (lhs := lhs) (rhs := rhs) hmem)

/-- Every HE `queryEquations` witness comes from a raw `(= lhs rhs)` rule that
already sits in LeaTTa's extracted translated rule surface; the freshened HE
match is therefore pinned to a concrete raw LeaTTa equation rule before any
alpha-boundary reasoning. -/
theorem queryEquations_extractRule_witness
    {space : Space} {atom rhs : Atom} {qb : Bindings} {fuel : Nat}
    (hmem : (rhs, qb) ∈ queryEquations space atom fuel) :
    ∃ idx lhs rawRhs,
      (Atom.expression [Atom.symbol "=", lhs, rawRhs], idx) ∈ space.atoms.zipIdx ∧
      (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) ∈
        Metta.Minimal.extractRules (toLeaTTaSpace space).atoms ∧
      FaithfulQueryWitness atom (freshenEquation idx lhs rawRhs fuel).1 qb fuel := by
  obtain ⟨eqidx, heqidx, lhs, rawRhs, hshape, _hRhs, hmatch⟩ :=
    mem_queryEquations_decompose hmem
  rcases eqidx with ⟨eq, idx⟩
  cases hshape
  have hrawMem : Atom.expression [Atom.symbol "=", lhs, rawRhs] ∈ space.atoms := by
    exact mem_of_mem_zipIdx (x := Atom.expression [Atom.symbol "=", lhs, rawRhs]) (i := idx) heqidx
  refine ⟨idx, lhs, rawRhs, ?_, ?_, hmatch⟩
  · simpa using heqidx
  · simpa [toLeaTTaSpace] using
      (mem_extractRules_of_mem_eq_atom (atoms := space.atoms) (lhs := lhs) (rhs := rawRhs) hrawMem)

/-- The visible-avoid query surface also pins every witness to a concrete raw
translated rule in LeaTTa's extracted rule set. This is the repaired-surface
analogue of `queryEquations_extractRule_witness`, ready for later transport
theorems that use the stronger freshness discipline. -/
theorem queryEquationsAgainstVisible_extractRule_witness
    {space : Space} {atom rhs : Atom} {qb : Bindings} {fuel : Nat}
    (hmem : (rhs, qb) ∈ queryEquationsAgainstVisible space atom fuel) :
    ∃ idx lhs rawRhs,
      (Atom.expression [Atom.symbol "=", lhs, rawRhs], idx) ∈ space.atoms.zipIdx ∧
      (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) ∈
        Metta.Minimal.extractRules (toLeaTTaSpace space).atoms ∧
      FaithfulQueryWitness atom
        (freshenEquationAgainst ((collectVars atom fuel).eraseDups) idx lhs rawRhs fuel).1
        qb fuel := by
  obtain ⟨eqidx, heqidx, lhs, rawRhs, hshape, _hRhs, hmatch⟩ :=
    mem_queryEquationsAgainstVisible_decompose hmem
  rcases eqidx with ⟨eq, idx⟩
  cases hshape
  have hrawMem : Atom.expression [Atom.symbol "=", lhs, rawRhs] ∈ space.atoms := by
    exact mem_of_mem_zipIdx
      (x := Atom.expression [Atom.symbol "=", lhs, rawRhs]) (i := idx) heqidx
  refine ⟨idx, lhs, rawRhs, ?_, ?_, hmatch⟩
  · simpa using heqidx
  · simpa [toLeaTTaSpace] using
      (mem_extractRules_of_mem_eq_atom (atoms := space.atoms) (lhs := lhs) (rhs := rawRhs) hrawMem)

/-- Public HE equation queries inherit the official matcher's invariant that
variable-variable matches are carried as equalities, not variable-valued
assignments. -/
theorem queryEquations_noVarAssignmentValues
    {space : Space} {atom rhs : Atom} {qb : Bindings} {fuel : Nat}
    (hmem : (rhs, qb) ∈ queryEquations space atom fuel) :
    NoVarAssignmentValues qb := by
  obtain ⟨_idx, _lhs, _rawRhs, _hzip, _hrule, hmatch⟩ :=
    queryEquations_extractRule_witness hmem
  exact faithfulQueryWitness_noVarAssignmentValues hmatch

/-- The visible-avoid query surface preserves the same equality-aware matcher
invariant. This is the repaired query path used by the conformance bridge. -/
theorem queryEquationsAgainstVisible_noVarAssignmentValues
    {space : Space} {atom rhs : Atom} {qb : Bindings} {fuel : Nat}
    (hmem : (rhs, qb) ∈ queryEquationsAgainstVisible space atom fuel) :
    NoVarAssignmentValues qb := by
  obtain ⟨_idx, _lhs, _rawRhs, _hzip, _hrule, hmatch⟩ :=
    queryEquationsAgainstVisible_extractRule_witness hmem
  exact faithfulQueryWitness_noVarAssignmentValues hmatch

/-- Public HE equation queries inherit assignment-key uniqueness from the
official matcher. -/
theorem queryEquations_assignmentsNodup
    {space : Space} {atom rhs : Atom} {qb : Bindings} {fuel : Nat}
    (hmem : (rhs, qb) ∈ queryEquations space atom fuel) :
    AssignmentsNodup qb := by
  obtain ⟨_idx, _lhs, _rawRhs, _hzip, _hrule, hmatch⟩ :=
    queryEquations_extractRule_witness hmem
  exact faithfulQueryWitness_assignmentsNodup hmatch

/-- The repaired visible-avoid query surface preserves assignment-key
uniqueness as part of the faithful HE query witness. -/
theorem queryEquationsAgainstVisible_assignmentsNodup
    {space : Space} {atom rhs : Atom} {qb : Bindings} {fuel : Nat}
    (hmem : (rhs, qb) ∈ queryEquationsAgainstVisible space atom fuel) :
    AssignmentsNodup qb := by
  obtain ⟨_idx, _lhs, _rawRhs, _hzip, _hrule, hmatch⟩ :=
    queryEquationsAgainstVisible_extractRule_witness hmem
  exact faithfulQueryWitness_assignmentsNodup hmatch

/-- Any HE equation-query witness also identifies the concrete raw translated
rule bucket that LeaTTa's indexed kernel will inspect for the same symbol-headed
query. This discharges the candidate-selection half of the equation bridge
directly from the HE witness, without assuming the later executable item
transport. -/
theorem queryEquations_extractCandidate_split
    {space : Space} {src rhs : Atom} {qb : Bindings} {fuel : Nat}
    {gt : Metta.GroundingTable} {k : String}
    (hk : Metta.Minimal.headKey (toLeaTTaAtom src) = some k)
    (hmem : (rhs, qb) ∈ queryEquations space src fuel) :
    ∃ idx lhs rawRhs pre post,
      (Atom.expression [Atom.symbol "=", lhs, rawRhs], idx) ∈ space.atoms.zipIdx ∧
      FaithfulQueryWitness src (freshenEquation idx lhs rawRhs fuel).1 qb fuel ∧
      Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          Metta.Minimal.World.empty (toLeaTTaAtom src) =
        pre ++ (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) :: post := by
  obtain ⟨idx, lhs, rawRhs, hzip, hrule, hmatch⟩ :=
    queryEquations_extractRule_witness hmem
  have hsrcHead : heHeadKey src = some k := by
    simpa [headKey_toLeaTTaAtom] using hk
  have hfreshHead :
      heHeadKey (freshenEquation idx lhs rawRhs fuel).1 = some k ∨
        heHeadKey (freshenEquation idx lhs rawRhs fuel).1 = none :=
    faithfulQueryWitness_headKey_compat hmatch hsrcHead
  have hlhsHead : heHeadKey lhs = some k ∨ heHeadKey lhs = none := by
    simpa [heHeadKey_freshenEquation_fst idx lhs rawRhs fuel] using hfreshHead
  have hcandCore :
      (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) ∈
        (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt).candidates
          (toLeaTTaAtom src) := by
    unfold Metta.Minimal.MinEnv.candidates
    rw [hk]
    cases hlhsHead with
    | inl hlhsSome =>
        have hbucket :
            (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) ∈
              (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt).ruleIndex.getD k [] := by
          rw [Metta.ruleIndex_getD]
          exact List.mem_filter.mpr ⟨hrule, by simp [headKey_toLeaTTaAtom, hlhsSome]⟩
        exact List.mem_append.mpr <| Or.inl hbucket
    | inr hlhsNone =>
        have hvar :
            (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) ∈
              (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt).varRules := by
          rw [Metta.ofAtomsGT_varRules]
          exact List.mem_filter.mpr ⟨hrule, by simp [headKey_toLeaTTaAtom, hlhsNone]⟩
        exact List.mem_append.mpr <| Or.inr hvar
  have hcand :
      (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) ∈
        Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          Metta.Minimal.World.empty (toLeaTTaAtom src) := by
    simpa [Metta.Minimal.candidatesW, Metta.Minimal.World.empty] using hcandCore
  rcases list_mem_split hcand with ⟨pre, post, hsplit⟩
  exact ⟨idx, lhs, rawRhs, pre, post, hzip, hmatch, hsplit⟩

/-- The repaired visible-avoid HE query surface also identifies the concrete
raw translated rule bucket that LeaTTa's indexed kernel will inspect for the
same symbol-headed query. This is the avoid-aware analogue of
`queryEquations_extractCandidate_split`, ready for the repaired transport
theorems. -/
theorem queryEquationsAgainstVisible_extractCandidate_split
    {space : Space} {src rhs : Atom} {qb : Bindings} {fuel : Nat}
    {gt : Metta.GroundingTable} {k : String}
    (hk : Metta.Minimal.headKey (toLeaTTaAtom src) = some k)
    (hmem : (rhs, qb) ∈ queryEquationsAgainstVisible space src fuel) :
    ∃ idx lhs rawRhs pre post,
      (Atom.expression [Atom.symbol "=", lhs, rawRhs], idx) ∈ space.atoms.zipIdx ∧
      FaithfulQueryWitness src
        (freshenEquationAgainst ((collectVars src fuel).eraseDups) idx lhs rawRhs fuel).1
        qb fuel ∧
      Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          Metta.Minimal.World.empty (toLeaTTaAtom src) =
        pre ++ (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) :: post := by
  obtain ⟨idx, lhs, rawRhs, hzip, hrule, hmatch⟩ :=
    queryEquationsAgainstVisible_extractRule_witness hmem
  have hsrcHead : heHeadKey src = some k := by
    simpa [headKey_toLeaTTaAtom] using hk
  have hfreshHead :
      heHeadKey
          (freshenEquationAgainst ((collectVars src fuel).eraseDups) idx lhs rawRhs fuel).1 =
            some k ∨
        heHeadKey
          (freshenEquationAgainst ((collectVars src fuel).eraseDups) idx lhs rawRhs fuel).1 =
            none :=
    faithfulQueryWitness_headKey_compat hmatch hsrcHead
  have hlhsHead : heHeadKey lhs = some k ∨ heHeadKey lhs = none := by
    simpa [heHeadKey_freshenEquationAgainst_fst ((collectVars src fuel).eraseDups) idx lhs rawRhs fuel]
      using hfreshHead
  have hcandCore :
      (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) ∈
        (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt).candidates
          (toLeaTTaAtom src) := by
    unfold Metta.Minimal.MinEnv.candidates
    rw [hk]
    cases hlhsHead with
    | inl hlhsSome =>
        have hbucket :
            (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) ∈
              (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt).ruleIndex.getD k [] := by
          rw [Metta.ruleIndex_getD]
          exact List.mem_filter.mpr ⟨hrule, by simp [headKey_toLeaTTaAtom, hlhsSome]⟩
        exact List.mem_append.mpr <| Or.inl hbucket
    | inr hlhsNone =>
        have hvar :
            (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) ∈
              (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt).varRules := by
          rw [Metta.ofAtomsGT_varRules]
          exact List.mem_filter.mpr ⟨hrule, by simp [headKey_toLeaTTaAtom, hlhsNone]⟩
        exact List.mem_append.mpr <| Or.inr hvar
  have hcand :
      (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) ∈
        Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          Metta.Minimal.World.empty (toLeaTTaAtom src) := by
    simpa [Metta.Minimal.candidatesW, Metta.Minimal.World.empty] using hcandCore
  rcases list_mem_split hcand with ⟨pre, post, hsplit⟩
  exact ⟨idx, lhs, rawRhs, pre, post, hzip, hmatch, hsplit⟩

/-- Candidate-selection half of the repaired visible-query bridge, factored at
the direct witness level.  A raw indexed HE equation plus its avoid-aware
faithful matcher witness already determines a candidate in LeaTTa's indexed
kernel for the same symbol-headed query; no executable matcher transport is
used here. -/
theorem candidate_split_of_againstVisible_witness
    {space : Space} {src lhs rawRhs : Atom} {qb : Bindings}
    {fuel : Nat} {gt : Metta.GroundingTable} {idx : Nat} {k : String}
    (hk : Metta.Minimal.headKey (toLeaTTaAtom src) = some k)
    (hzip : (Atom.expression [Atom.symbol "=", lhs, rawRhs], idx) ∈
      space.atoms.zipIdx)
    (hmatch : FaithfulQueryWitness src
      (freshenEquationAgainst ((collectVars src fuel).eraseDups) idx lhs rawRhs fuel).1
      qb fuel) :
    ∃ pre post,
      Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          Metta.Minimal.World.empty (toLeaTTaAtom src) =
        pre ++ (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) :: post := by
  have hRawMem : Atom.expression [Atom.symbol "=", lhs, rawRhs] ∈ space.atoms := by
    exact mem_of_mem_zipIdx
      (x := Atom.expression [Atom.symbol "=", lhs, rawRhs]) (i := idx) hzip
  have hrule :
      (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) ∈
        Metta.Minimal.extractRules (toLeaTTaSpace space).atoms := by
    simpa [toLeaTTaSpace] using
      (mem_extractRules_of_mem_eq_atom
        (atoms := space.atoms) (lhs := lhs) (rhs := rawRhs) hRawMem)
  have hsrcHead : heHeadKey src = some k := by
    simpa [headKey_toLeaTTaAtom] using hk
  have hfreshHead :
      heHeadKey
          (freshenEquationAgainst ((collectVars src fuel).eraseDups) idx lhs rawRhs fuel).1 =
            some k ∨
        heHeadKey
          (freshenEquationAgainst ((collectVars src fuel).eraseDups) idx lhs rawRhs fuel).1 =
            none :=
    faithfulQueryWitness_headKey_compat hmatch hsrcHead
  have hlhsHead : heHeadKey lhs = some k ∨ heHeadKey lhs = none := by
    simpa [heHeadKey_freshenEquationAgainst_fst
        ((collectVars src fuel).eraseDups) idx lhs rawRhs fuel]
      using hfreshHead
  have hcandCore :
      (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) ∈
        (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt).candidates
          (toLeaTTaAtom src) := by
    unfold Metta.Minimal.MinEnv.candidates
    rw [hk]
    cases hlhsHead with
    | inl hlhsSome =>
        have hbucket :
            (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) ∈
              (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt).ruleIndex.getD k [] := by
          rw [Metta.ruleIndex_getD]
          exact List.mem_filter.mpr ⟨hrule, by simp [headKey_toLeaTTaAtom, hlhsSome]⟩
        exact List.mem_append.mpr <| Or.inl hbucket
    | inr hlhsNone =>
        have hvar :
            (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) ∈
              (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt).varRules := by
          rw [Metta.ofAtomsGT_varRules]
          exact List.mem_filter.mpr ⟨hrule, by simp [headKey_toLeaTTaAtom, hlhsNone]⟩
        exact List.mem_append.mpr <| Or.inr hvar
  have hcand :
      (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) ∈
        Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          Metta.Minimal.World.empty (toLeaTTaAtom src) := by
    simpa [Metta.Minimal.candidatesW, Metta.Minimal.World.empty] using hcandCore
  rcases list_mem_split hcand with ⟨pre, post, hsplit⟩
  exact ⟨pre, post, hsplit⟩

/-- Every faithful HE equation-query witness has passed the public loop filter.
The stronger assignment-key uniqueness invariant is a separate matcher/merge
theorem; consumers that need it should keep it as an explicit fragment
hypothesis. -/
theorem queryEquations_hasLoop_false
    {space : Space} {atom rhs : Atom} {qb : Bindings} {fuel : Nat}
    (hmem : (rhs, qb) ∈ queryEquations space atom fuel) :
    qb.hasLoop = false := by
  obtain ⟨_, _, _, _, _, hfw⟩ := mem_queryEquations_decompose hmem
  rcases hfw with ⟨_, _hmb, hmergeLoop⟩
  exact hmergeLoop.2.2

/-- The repaired visible-avoid query surface inherits the same loop-freedom
fact from the public filter. -/
theorem queryEquationsAgainstVisible_hasLoop_false
    {space : Space} {atom rhs : Atom} {qb : Bindings} {fuel : Nat}
    (hmem : (rhs, qb) ∈ queryEquationsAgainstVisible space atom fuel) :
    qb.hasLoop = false := by
  obtain ⟨_, _, _, _, _, hfw⟩ := mem_queryEquationsAgainstVisible_decompose hmem
  rcases hfw with ⟨_, _hmb, hmergeLoop⟩
  exact hmergeLoop.2.2

/-- Explicit alpha-boundary package for `queryEquations`: once the fuel reaches
the relevant term depths, the HE freshened rule seen by the matcher is exactly
the LeaTTa translation of the raw rule under the same renaming. This makes the
freshening mismatch visible instead of pretending it vanished. -/
theorem queryEquations_alphaBoundary
    {space : Space} {atom rhs : Atom} {qb : Bindings} {fuel : Nat}
    (hmem : (rhs, qb) ∈ queryEquations space atom fuel) :
    ∃ idx lhs rawRhs,
      (Atom.expression [Atom.symbol "=", lhs, rawRhs], idx) ∈ space.atoms.zipIdx ∧
      (atomDepth lhs + 1 ≤ fuel →
        toLeaTTaAtom (freshenEquation idx lhs rawRhs fuel).1 =
          Metta.renameVars
            ((freshMapping idx ((collectVars lhs fuel ++ collectVars rawRhs fuel).eraseDups)).1)
            (toLeaTTaAtom lhs)) ∧
      (atomDepth rawRhs + 1 ≤ fuel →
        toLeaTTaAtom rhs =
          Metta.renameVars
            ((freshMapping idx ((collectVars lhs fuel ++ collectVars rawRhs fuel).eraseDups)).1)
            (toLeaTTaAtom rawRhs)) := by
  obtain ⟨eqidx, heqidx, lhs, rawRhs, hshape, hRhs, _hmatch⟩ :=
    mem_queryEquations_decompose hmem
  rcases eqidx with ⟨eq, idx⟩
  cases hshape
  refine ⟨idx, lhs, rawRhs, ?_, ?_, ?_⟩
  · simpa using heqidx
  · intro hdepth
    exact toLeaTTaAtom_freshenEquation_fst idx lhs rawRhs fuel hdepth
  · intro hdepth
    simpa [hRhs] using toLeaTTaAtom_freshenEquation_snd idx lhs rawRhs fuel hdepth

/-- The repaired visible-avoid query surface has the same exact translation
boundary shape: once the fuel reaches the relevant depths, the HE freshened
rule seen by the matcher is exactly the LeaTTa translation of the raw rule
under the avoid-aware HE renaming. This packages the stronger freshness
discipline in the same form as `queryEquations_alphaBoundary`, so later
transport proofs can reuse the same translation skeleton on the repaired
surface. -/
theorem queryEquationsAgainstVisible_alphaBoundary
    {space : Space} {atom rhs : Atom} {qb : Bindings} {fuel : Nat}
    (hmem : (rhs, qb) ∈ queryEquationsAgainstVisible space atom fuel) :
    ∃ idx lhs rawRhs,
      (Atom.expression [Atom.symbol "=", lhs, rawRhs], idx) ∈ space.atoms.zipIdx ∧
      (atomDepth lhs + 1 ≤ fuel →
        toLeaTTaAtom (freshenEquationAgainst ((collectVars atom fuel).eraseDups) idx lhs rawRhs fuel).1 =
          Metta.renameVars
            ((freshMappingAgainst idx ((collectVars atom fuel).eraseDups)
              ((collectVars lhs fuel ++ collectVars rawRhs fuel).eraseDups)).1)
            (toLeaTTaAtom lhs)) ∧
      (atomDepth rawRhs + 1 ≤ fuel →
        toLeaTTaAtom rhs =
          Metta.renameVars
            ((freshMappingAgainst idx ((collectVars atom fuel).eraseDups)
              ((collectVars lhs fuel ++ collectVars rawRhs fuel).eraseDups)).1)
            (toLeaTTaAtom rawRhs)) := by
  obtain ⟨eqidx, heqidx, lhs, rawRhs, hshape, hRhs, _hmatch⟩ :=
    mem_queryEquationsAgainstVisible_decompose hmem
  rcases eqidx with ⟨eq, idx⟩
  cases hshape
  refine ⟨idx, lhs, rawRhs, ?_, ?_, ?_⟩
  · simpa using heqidx
  · intro hdepth
    exact
      toLeaTTaAtom_freshenEquationAgainst_fst
        ((collectVars atom fuel).eraseDups) idx lhs rawRhs fuel hdepth
  · intro hdepth
    simpa [hRhs] using
      toLeaTTaAtom_freshenEquationAgainst_snd
        ((collectVars atom fuel).eraseDups) idx lhs rawRhs fuel hdepth

/-- Once a translated LeaTTa rule-and-match witness has been transported, it
fires in LeaTTa's published QUERY relation. This isolates the remaining proof
work: after witness transport, equation-fragment simulation is just this final
membership step plus the head-key side condition. -/
theorem mem_equalityReductions_of_extractRule_match
    {space : Space} {src dst : Atom} {lhs rhs : Metta.Atom} {mb : Metta.Bindings}
    (hrule : (lhs, rhs) ∈ Metta.Minimal.extractRules (toLeaTTaSpace space).atoms)
    (hmatch : mb ∈ Metta.matchAtoms lhs (toLeaTTaAtom src))
    (hres : toLeaTTaAtom dst = Metta.instantiate mb rhs) :
    toLeaTTaAtom dst ∈ Metta.equalityReductions (toLeaTTaSpace space) (toLeaTTaAtom src) := by
  rw [Metta.mem_equalityReductions]
  refine ⟨(lhs, rhs), ?_, mb, hmatch, hres⟩
  simpa [extractRules_eq_equalityRules space] using hrule

/-- Positive exact fragment: if a ground `(= lhs rhs)` rule contributes a
successful HE query branch, then the translated RHS already lies in LeaTTa's
published raw QUERY reduct set. This is the honest exact theorem that survives
the freshening boundary because both sides of the rule are closed. -/
theorem mem_equalityReductions_of_ground_rule_query
    {space : Space} {src lhs rawRhs : Atom} {qb : Bindings} {fuel idx : Nat}
    (hzip : (Atom.expression [Atom.symbol "=", lhs, rawRhs], idx) ∈ space.atoms.zipIdx)
    (hLhsGround : GroundAtom lhs) (hRhsGround : GroundAtom rawRhs)
    (hmatch :
      simpleMatch (freshenEquation idx lhs rawRhs fuel).1 src Bindings.empty fuel = some qb) :
    toLeaTTaAtom rawRhs ∈
      Metta.equalityReductions (toLeaTTaSpace space) (toLeaTTaAtom src) := by
  have hfresh : freshenEquation idx lhs rawRhs fuel = (lhs, rawRhs) :=
    freshenEquation_eq_of_ground idx hLhsGround hRhsGround fuel
  have hmatchRaw : simpleMatch lhs src Bindings.empty fuel = some qb := by
    simpa [hfresh] using hmatch
  obtain ⟨hqb, hmb⟩ := (simpleMatch_ground_empty_exact fuel).1 hLhsGround hmatchRaw
  subst hqb
  have hRawMem : Atom.expression [Atom.symbol "=", lhs, rawRhs] ∈ space.atoms := by
    exact mem_of_mem_zipIdx (x := Atom.expression [Atom.symbol "=", lhs, rawRhs]) (i := idx) hzip
  have hrule :
      (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) ∈
        Metta.Minimal.extractRules (toLeaTTaSpace space).atoms := by
    simpa [toLeaTTaSpace] using
      (mem_extractRules_of_mem_eq_atom
        (atoms := space.atoms) (lhs := lhs) (rhs := rawRhs) hRawMem)
  refine mem_equalityReductions_of_extractRule_match hrule hmb ?_
  simpa [Metta.Bindings.empty] using (Metta.instantiate_nil (toLeaTTaAtom rawRhs)).symm

/-- The one-candidate worklist generated by LeaTTa's capture-avoiding `queryOp` fold step.
This compatibility name is definitionally the executable helper, so bridge proofs cannot drift
from the runtime freshening policy. -/
abbrev queryOpItemsOfRule (prev : Metta.Minimal.Stack) (toEval : Metta.Atom)
    (b : Metta.Bindings) (counter : Nat) (p : Metta.Atom × Metta.Atom) :
    List Metta.Minimal.Item :=
  Metta.Minimal.queryOpItemsOfRule prev toEval b counter p

/-- With no incoming stack or bindings and a closed query atom, the repaired freshener takes its
legacy branch. This is the compatibility fact used by the old closed-query regression tranche. -/
theorem freshenRuleAvoiding_eq_legacy_empty_of_target_vars_nil
    (counter : Nat) (target lhs rhs : Metta.Atom) (htarget : target.vars = []) :
    Metta.Minimal.freshenRuleAvoiding counter
        (Metta.Minimal.queryOpAvoid [] target Metta.Bindings.empty) lhs rhs =
      (Metta.Minimal.freshenRule counter lhs rhs, counter + 1) := by
  apply Metta.Minimal.freshenRuleAvoiding_eq_legacy
  simp [Metta.Minimal.queryOpAvoid, Metta.Bindings.empty, Metta.Bindings.vars,
    Metta.Minimal.liveStackVars, htarget]

/-- Exact membership characterization for the one-candidate executable
`queryOp` layer.  Every emitted item comes from the candidate's runtime
freshened LHS/RHS, a LeaTTa matcher result, a surviving ambient merge, loop
filtering, and instantiation of the freshened RHS. -/
theorem mem_queryOpItemsOfRule_iff
    (prev : Metta.Minimal.Stack) (toEval : Metta.Atom)
    (b : Metta.Bindings) (counter : Nat) (p : Metta.Atom × Metta.Atom)
    (item : Metta.Minimal.Item) :
    item ∈ queryOpItemsOfRule prev toEval b counter p ↔
      ∃ mb ∈ Metta.matchAtoms
            (Metta.Minimal.freshenRuleAvoiding counter
              (Metta.Minimal.queryOpAvoid prev toEval b) p.1 p.2).1.1 toEval,
        ∃ m ∈ Metta.Bindings.merge b mb,
          Metta.Bindings.hasLoop m = false ∧
            item = Metta.Minimal.evalResult prev
              (Metta.instantiate m
                (Metta.Minimal.freshenRuleAvoiding counter
                  (Metta.Minimal.queryOpAvoid prev toEval b) p.1 p.2).1.2) m := by
  unfold queryOpItemsOfRule Metta.Minimal.queryOpItemsOfRule
  cases hfr : (Metta.Minimal.freshenRuleAvoiding counter
      (Metta.Minimal.queryOpAvoid prev toEval b) p.1 p.2).1 with
  | mk lhs' rhs' =>
      simp only [List.mem_flatMap, List.mem_filterMap]
      constructor
      · intro h
        rcases h with ⟨mb, hmb, m, hm, hitem⟩
        by_cases hloop : Metta.Bindings.hasLoop m
        · simp [hloop] at hitem
        · simp [hloop] at hitem
          exact ⟨mb, hmb, m, hm, by simpa using hloop, hitem.symm⟩
      · intro h
        rcases h with ⟨mb, hmb, m, hm, hloop, heq⟩
        exact ⟨mb, hmb, m, hm, by simp [hloop, heq]⟩

/-- The accumulator step inside `queryOp`, factored out so membership can be tracked
through the candidate fold directly. -/
private abbrev queryOpFoldStep (prev : Metta.Minimal.Stack) (toEval : Metta.Atom)
    (b : Metta.Bindings) :
    (List Metta.Minimal.Item × Metta.Minimal.St) →
      (Metta.Atom × Metta.Atom) →
      (List Metta.Minimal.Item × Metta.Minimal.St) :=
  Metta.Minimal.queryOpFoldStep prev toEval b

/-- Once an item has entered the `queryOp` accumulator, later candidates cannot remove it. -/
private theorem queryOpFold_preserves_mem (prev : Metta.Minimal.Stack) (toEval : Metta.Atom)
    (b : Metta.Bindings) :
    ∀ cs acc st item,
      item ∈ acc →
        item ∈ ((List.foldl (queryOpFoldStep prev toEval b) (acc, st) cs).1) := by
  intro cs
  induction cs with
  | nil =>
      intro acc st item hmem
      simpa
  | cons p ps ih =>
      intro acc st item hmem
      simp only [List.foldl_cons]
      exact ih _ _ _ (by simp [hmem])

/-- Processing `n` candidates in `queryOp` advances only the gensym counter, by `n`. -/
private theorem queryOpFold_counter (prev : Metta.Minimal.Stack) (toEval : Metta.Atom)
    (b : Metta.Bindings) :
    ∀ cs acc st,
      ((List.foldl (queryOpFoldStep prev toEval b) (acc, st) cs).2).counter =
        st.counter + List.length cs := by
  intro cs
  induction cs with
  | nil =>
      intro acc st
      simp
  | cons p ps ih =>
      intro acc st
      simp only [List.foldl_cons, queryOpFoldStep, Metta.Minimal.queryOpFoldStep]
      rw [Metta.Minimal.freshenRuleAvoiding_counter]
      simp [ih, Nat.add_comm, Nat.add_left_comm]

/-- If the candidate list is split as `pre ++ p :: post`, and `p` contributes a given
item when processed at its actual fold counter, then that item survives into the final
`queryOp` candidate fold results. -/
private theorem mem_queryOpFold_of_split_candidate
    (prev : Metta.Minimal.Stack) (toEval : Metta.Atom) (b : Metta.Bindings)
    (st : Metta.Minimal.St)
    (pre post : List (Metta.Atom × Metta.Atom)) (p : Metta.Atom × Metta.Atom)
    (item : Metta.Minimal.Item)
    (hitem :
      item ∈ queryOpItemsOfRule prev toEval b (st.counter + pre.length) p) :
    item ∈
      (((pre ++ p :: post).foldl (queryOpFoldStep prev toEval b) ([], st)).1) := by
  rw [List.foldl_append]
  let prefixAcc := pre.foldl (queryOpFoldStep prev toEval b) ([], st)
  have hcounter : prefixAcc.2.counter = st.counter + pre.length := by
    simpa [prefixAcc] using queryOpFold_counter prev toEval b pre [] st
  simp only [List.foldl_cons]
  have hseed :
      item ∈ prefixAcc.1 ++ queryOpItemsOfRule prev toEval b prefixAcc.2.counter p := by
    simp [hcounter, hitem]
  exact queryOpFold_preserves_mem prev toEval b post _ _ _ hseed

/-- Purely operational lift: once we know which candidate split `queryOp` will
process and that the candidate's one-step worklist already contains `item` at
its actual fold counter, the final executable `queryOp` output contains `item`
as well. This packages all remaining fold/`isEmpty` bookkeeping so the
non-ground bridge can focus on transporting the freshened witness itself. This
is intentionally reusable by later canonical/avoid-aware bridge modules. -/
theorem queryOp_contains_item_of_splitCandidate
    (env : Metta.Minimal.MinEnv) (st : Metta.Minimal.St)
    (prev : Metta.Minimal.Stack) (toEval : Metta.Atom) (b : Metta.Bindings)
    {pre post : List (Metta.Atom × Metta.Atom)} {p : Metta.Atom × Metta.Atom}
    {item : Metta.Minimal.Item}
    (hNotVarHead : Metta.Minimal.isVariableHeaded toEval = false)
    (hsplit : Metta.Minimal.candidatesW env st.world toEval = pre ++ p :: post)
    (hitem : item ∈ queryOpItemsOfRule prev toEval b (st.counter + pre.length) p) :
    item ∈ (Metta.Minimal.queryOp env st prev toEval b).1 := by
  have hmemResults :
      item ∈
        ((Metta.Minimal.candidatesW env st.world toEval).foldl
          (queryOpFoldStep prev toEval b) ([], st)).1 := by
    rw [hsplit]
    simpa using
      (mem_queryOpFold_of_split_candidate prev toEval b st pre post p item hitem)
  set folded : List Metta.Minimal.Item × Metta.Minimal.St :=
    (Metta.Minimal.candidatesW env st.world toEval).foldl
      (queryOpFoldStep prev toEval b) ([], st)
  have hfoldedMem : item ∈ folded.1 := by
    simpa [folded] using hmemResults
  have hnonempty : folded.1.isEmpty = false := by
    cases hlist : folded.1 with
    | nil => simp [hlist] at hfoldedMem
    | cons _ _ => simp
  have hqueryOpResults :
      (Metta.Minimal.queryOp env st prev toEval b).1 = folded.1 := by
    unfold Metta.Minimal.queryOp
    rw [hNotVarHead]
    change
      (if folded.1.isEmpty then
          ([Metta.Minimal.finItem prev Metta.Minimal.notReducibleA b], folded.2)
        else folded).1 = folded.1
    simp [hnonempty]
  rw [hqueryOpResults]
  exact hfoldedMem

/-- On the exact closed-ground fragment, an HE equation-query witness already appears on
LeaTTa's executable `queryOp` surface: the same translated ground rule survives
candidate selection, freshening is inert, matching yields the empty binding witness,
and the resulting item is emitted by the candidate fold. This is the first honest
positive bridge to the real `queryOp` layer rather than raw `equalityReductions`. -/
theorem queryOp_contains_ground_rule_result
    {space : Space} {src lhs rawRhs : Atom} {qb : Bindings} {fuel idx : Nat}
    {gt : Metta.GroundingTable} {k : String}
    (prev : Metta.Minimal.Stack) (counter : Nat)
    (hk : Metta.Minimal.headKey (toLeaTTaAtom src) = some k)
    (hzip : (Atom.expression [Atom.symbol "=", lhs, rawRhs], idx) ∈ space.atoms.zipIdx)
    (hLhsGround : GroundAtom lhs) (hRhsGround : GroundAtom rawRhs)
    (hmatch :
      simpleMatch (freshenEquation idx lhs rawRhs fuel).1 src Bindings.empty fuel = some qb) :
    Metta.Minimal.evalResult prev (toLeaTTaAtom rawRhs) Metta.Bindings.empty ∈
      (Metta.Minimal.queryOp
        (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
        { counter := counter, world := Metta.Minimal.World.empty }
        prev (toLeaTTaAtom src) Metta.Bindings.empty).1 := by
  let env := Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt
  let st0 : Metta.Minimal.St := { counter := counter, world := Metta.Minimal.World.empty }
  have hfreshHE : freshenEquation idx lhs rawRhs fuel = (lhs, rawRhs) :=
    freshenEquation_eq_of_ground idx hLhsGround hRhsGround fuel
  have hmatchRaw : simpleMatch lhs src Bindings.empty fuel = some qb := by
    simpa [hfreshHE] using hmatch
  obtain ⟨hqb, hmb⟩ := (simpleMatch_ground_empty_exact fuel).1 hLhsGround hmatchRaw
  subst hqb
  have hRawMem : Atom.expression [Atom.symbol "=", lhs, rawRhs] ∈ space.atoms := by
    exact mem_of_mem_zipIdx (x := Atom.expression [Atom.symbol "=", lhs, rawRhs]) (i := idx) hzip
  have hrule :
      (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) ∈
        Metta.Minimal.extractRules (toLeaTTaAtoms space.atoms) := by
    exact mem_extractRules_of_mem_eq_atom (atoms := space.atoms) (lhs := lhs) (rhs := rawRhs) hRawMem
  have hcandCore :
      (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) ∈ env.candidates (toLeaTTaAtom src) := by
    exact Metta.candidates_complete (toLeaTTaAtoms space.atoms) gt (toLeaTTaAtom src) k
      (toLeaTTaAtom lhs) (toLeaTTaAtom rawRhs) hk hrule (by
        intro hnil
        rw [hnil] at hmb
        simp at hmb)
  have hcand :
      (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) ∈
        Metta.Minimal.candidatesW env Metta.Minimal.World.empty (toLeaTTaAtom src) := by
    simpa [env, Metta.Minimal.candidatesW, Metta.Minimal.World.empty] using hcandCore
  rcases list_mem_split hcand with ⟨pre, post, hsplit⟩
  have hvarsL : (toLeaTTaAtom lhs).vars = [] :=
    toLeaTTaAtom_vars_nil_of_ground hLhsGround
  have hvarsR : (toLeaTTaAtom rawRhs).vars = [] :=
    toLeaTTaAtom_vars_nil_of_ground hRhsGround
  have hitem :
      Metta.Minimal.evalResult prev (toLeaTTaAtom rawRhs) Metta.Bindings.empty ∈
        queryOpItemsOfRule prev (toLeaTTaAtom src) Metta.Bindings.empty
          (counter + pre.length)
          (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) := by
    have hfreshLea :
        Metta.Minimal.freshenRule
            (counter + pre.length)
            (toLeaTTaAtom lhs) (toLeaTTaAtom rawRhs) =
          (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) := by
      simp [Metta.Minimal.freshenRule, hvarsL, hvarsR]
    have hcompat :
        Metta.Minimal.freshenRuleAvoiding (counter + pre.length)
            (Metta.Minimal.queryOpAvoid prev (toLeaTTaAtom src) Metta.Bindings.empty)
            (toLeaTTaAtom lhs) (toLeaTTaAtom rawRhs) =
          (Metta.Minimal.freshenRule (counter + pre.length)
            (toLeaTTaAtom lhs) (toLeaTTaAtom rawRhs), counter + pre.length + 1) := by
      apply Metta.Minimal.freshenRuleAvoiding_eq_legacy
      rw [hfreshLea, hvarsL, hvarsR]
      simp
    unfold queryOpItemsOfRule Metta.Minimal.queryOpItemsOfRule
    rw [hcompat, hfreshLea]
    refine List.mem_flatMap.mpr ?_
    refine ⟨Metta.Bindings.empty, hmb, ?_⟩
    simp [Metta.Bindings.empty, merge_empty_right,
      Metta.Minimal.evalResult, Metta.instantiate_nil]
  have hmemResults :
      Metta.Minimal.evalResult prev (toLeaTTaAtom rawRhs) Metta.Bindings.empty ∈
        ((Metta.Minimal.candidatesW env Metta.Minimal.World.empty (toLeaTTaAtom src)).foldl
          (queryOpFoldStep prev (toLeaTTaAtom src) Metta.Bindings.empty) ([], st0)).1 := by
    rw [hsplit]
    simpa [st0] using
      (mem_queryOpFold_of_split_candidate prev (toLeaTTaAtom src) Metta.Bindings.empty st0
        pre post (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs)
        (Metta.Minimal.evalResult prev (toLeaTTaAtom rawRhs) Metta.Bindings.empty) hitem)
  have hNotVarHead : Metta.Minimal.isVariableHeaded (toLeaTTaAtom src) = false := by
    rcases Metta.headKey_some hk with hsrc | ⟨ls, hsrc⟩
    · rw [hsrc]
      simp [Metta.Minimal.isVariableHeaded]
    · rw [hsrc]
      simp [Metta.Minimal.isVariableHeaded]
  exact
    queryOp_contains_item_of_splitCandidate env st0 prev
      (toLeaTTaAtom src) Metta.Bindings.empty hNotVarHead hsplit hitem

/-- Typed specialization of the exact closed-ground `queryOp` bridge. On this
fragment the translated rule is already closed, so the LeaTTa preservation
hypothesis package collapses to the empty-context case: if the translated rule
is well-typed on both sides under a fixed LeaTTa `TypeEnv`, then the emitted
`queryOp` item is present and carries that same type. -/
theorem queryOp_contains_typed_ground_rule_result
    {space : Space} {src lhs rawRhs : Atom} {qb : Bindings} {fuel idx : Nat}
    {gt : Metta.GroundingTable} {k : String}
    {env : Metta.TypeEnv} {T : Metta.Atom}
    (prev : Metta.Minimal.Stack) (counter : Nat)
    (hk : Metta.Minimal.headKey (toLeaTTaAtom src) = some k)
    (hzip : (Atom.expression [Atom.symbol "=", lhs, rawRhs], idx) ∈ space.atoms.zipIdx)
    (hLhsGround : GroundAtom lhs) (hRhsGround : GroundAtom rawRhs)
    (hmatch :
      simpleMatch (freshenEquation idx lhs rawRhs fuel).1 src Bindings.empty fuel = some qb)
    (hL : Metta.WT env [] (toLeaTTaAtom lhs) T)
    (hR : Metta.WT env [] (toLeaTTaAtom rawRhs) T) :
    ∃ emitted m,
      Metta.Minimal.evalResult prev emitted m ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (toLeaTTaAtom src) Metta.Bindings.empty).1 ∧
      emitted = toLeaTTaAtom rawRhs ∧
      Metta.WT env [] emitted T := by
  have hitem :=
    queryOp_contains_ground_rule_result
      (space := space) (src := src) (lhs := lhs) (rawRhs := rawRhs)
      (qb := qb) (fuel := fuel) (idx := idx) (gt := gt) (k := k)
      prev counter hk hzip hLhsGround hRhsGround hmatch
  have htypedInst :
      Metta.WT env [] (toLeaTTaAtom rawRhs) T := by
    have htyped :=
      instantiated_rule_typed_of_reduction_preserves_type
        (env := env) (Γ := []) (lhs := lhs) (rhs := rawRhs)
        (qb := Bindings.empty) (T := T)
        (hσ := grounds_nil env (toLeaTTaSubst Bindings.empty.assignments))
        (hL := hL) (hR := hR) GroundBindings.empty AssignmentsNodup.empty
    simpa [toLeaTTaMatchBindings_empty, Metta.instantiate_nil] using htyped.2
  exact ⟨toLeaTTaAtom rawRhs, Metta.Bindings.empty, hitem, rfl, htypedInst⟩

/-- Exact remaining transport obligation for the non-ground equation fragment.
Once an HE `queryEquations` witness is decomposed to its concrete indexed raw
rule, the only missing bridge step is to show that the corresponding LeaTTa
freshened candidate contributes the translated HE result item at the exact
candidate-fold counter where `queryOp` processes that rule. The counter
alignment is real semantic content here: `queryOp` freshens by its runtime
counter, while HE freshens from the equation witness index. Everything after
that is just the operational bookkeeping handled by
`queryOp_contains_item_of_splitCandidate`. -/
def QueryOpWitnessTransport
    (space : Space) (src rhs : Atom) (qb : Bindings) (fuel : Nat)
    (gt : Metta.GroundingTable) (prev : Metta.Minimal.Stack) (counter : Nat) : Prop :=
  ∀ {idx lhs rawRhs k}
    (_hk : Metta.Minimal.headKey (toLeaTTaAtom src) = some k)
    (_hzip : (Atom.expression [Atom.symbol "=", lhs, rawRhs], idx) ∈ space.atoms.zipIdx)
    (_hmatch : FaithfulQueryWitness src (freshenEquation idx lhs rawRhs fuel).1 qb fuel),
    ∃ pre post,
      Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          Metta.Minimal.World.empty (toLeaTTaAtom src) =
        pre ++ (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) :: post ∧
      Metta.Minimal.evalResult prev (toLeaTTaAtom rhs) (toLeaTTaMatchBindings qb) ∈
        queryOpItemsOfRule prev (toLeaTTaAtom src) Metta.Bindings.empty (counter + pre.length)
          (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs)

/-- Honest reduction of the remaining non-ground positive bridge: if the
specialized freshened-witness transport above is provided, then the translated
HE query result already appears on LeaTTa's executable `queryOp` surface. This
isolates the proof debt to one named transport lemma rather than scattering it
through the operational proof. -/
theorem queryOp_contains_queryEquations_result_of_transport
    {space : Space} {src rhs : Atom} {qb : Bindings} {fuel : Nat}
    {gt : Metta.GroundingTable} {k : String}
    (prev : Metta.Minimal.Stack) (counter : Nat)
    (hk : Metta.Minimal.headKey (toLeaTTaAtom src) = some k)
    (hquery : (rhs, qb) ∈ queryEquations space src fuel)
    (htransport : QueryOpWitnessTransport space src rhs qb fuel gt prev counter) :
    Metta.Minimal.evalResult prev (toLeaTTaAtom rhs) (toLeaTTaMatchBindings qb) ∈
      (Metta.Minimal.queryOp
        (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
        { counter := counter, world := Metta.Minimal.World.empty }
        prev (toLeaTTaAtom src) Metta.Bindings.empty).1 := by
  let env := Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt
  let st0 : Metta.Minimal.St := { counter := counter, world := Metta.Minimal.World.empty }
  obtain ⟨idx, lhs, rawRhs, hzip, _hrule, hmatch⟩ :=
    queryEquations_extractRule_witness hquery
  obtain ⟨pre, post, hsplit, hitem⟩ := htransport hk hzip hmatch
  have hNotVarHead : Metta.Minimal.isVariableHeaded (toLeaTTaAtom src) = false := by
    rcases Metta.headKey_some hk with hsrc | ⟨ls, hsrc⟩
    · rw [hsrc]
      simp [Metta.Minimal.isVariableHeaded]
    · rw [hsrc]
      simp [Metta.Minimal.isVariableHeaded]
  exact
    queryOp_contains_item_of_splitCandidate env st0 prev
      (toLeaTTaAtom src) Metta.Bindings.empty hNotVarHead hsplit hitem

/-- Rule-level name for the one honest remaining positive non-ground bridge
hypothesis. This stays deliberately at the `queryOp` item layer: `queryOp`
emits executable work items, not already-collapsed visible HE atoms. -/
abbrev EquationMatchQueryOpTransport
    {space : Space} {src rhs : Atom} {qb : Bindings} {fuel : Nat}
    {gt : Metta.GroundingTable}
    (prev : Metta.Minimal.Stack) (counter : Nat) : Prop :=
  QueryOpWitnessTransport space src rhs qb fuel gt prev counter

/-- Honest positive `equation_match → queryOp` theorem at the executable item
layer. Once the specialized non-ground witness transport is supplied as the
single named hypothesis above, the corresponding translated query result item
already appears on LeaTTa's `queryOp` surface. -/
theorem queryOp_contains_equation_match_item_of_transport
    {space : Space} {src rhs : Atom} {qb : Bindings} {fuel : Nat}
    {gt : Metta.GroundingTable} {k : String}
    (prev : Metta.Minimal.Stack) (counter : Nat)
    (hk : Metta.Minimal.headKey (toLeaTTaAtom src) = some k)
    (hquery : (rhs, qb) ∈ queryEquations space src fuel)
    (htransport : EquationMatchQueryOpTransport
      (space := space) (src := src) (rhs := rhs) (qb := qb) (fuel := fuel)
      (gt := gt) prev counter) :
    Metta.Minimal.evalResult prev (toLeaTTaAtom rhs) (toLeaTTaMatchBindings qb) ∈
      (Metta.Minimal.queryOp
        (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
        { counter := counter, world := Metta.Minimal.World.empty }
        prev (toLeaTTaAtom src) Metta.Bindings.empty).1 := by
  exact
    queryOp_contains_queryEquations_result_of_transport
      (space := space) (src := src) (rhs := rhs) (qb := qb) (fuel := fuel)
      (gt := gt) (k := k) prev counter hk hquery htransport

/-- Honest visible-successor bridge on the fragment where HE's recursive
application agrees with LeaTTa's one-pass matcher instantiation: if the
translated instantiated RHS item is already present on LeaTTa's executable
`queryOp` surface, then the visible HE `equation_match` successor is present as
well, up to α-equivalence. This avoids the false general target
`QueryOpWitnessTransport` used to aim at: the runtime emits the instantiated
RHS, not the freshened raw RHS. -/
theorem queryOp_contains_equation_match_visible_successor_of_instantiated_item
    {space : Space} {src rhs : Atom} {qb : Bindings} {fuel : Nat}
    {gt : Metta.GroundingTable}
    (prev : Metta.Minimal.Stack) (counter : Nat)
    (_hquery : (rhs, qb) ∈ queryEquations space src fuel)
    (heq : qb.equalities = [])
    (hno : NoVarAssignmentValues qb)
    (hkeys : AssignmentsNodup qb)
    (hfresh : ValueKeysFreshForValues (toLeaTTaMatchBindings qb))
    (hdepth : atomDepth rhs + 2 ≤ fuel)
    (hitem :
      Metta.Minimal.evalResult prev
          (Metta.instantiate (toLeaTTaMatchBindings qb) (toLeaTTaAtom rhs))
          (toLeaTTaMatchBindings qb) ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (toLeaTTaAtom src) Metta.Bindings.empty).1) :
    ∃ emitted m,
      Metta.Minimal.evalResult prev emitted m ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (toLeaTTaAtom src) Metta.Bindings.empty).1 ∧
      Metta.AlphaEq emitted (toLeaTTaAtom (qb.applyFull rhs fuel)) := by
  exact
    visible_successor_of_instantiated_item
      heq hno hkeys hfresh hdepth hitem

/-- The same instantiated-item visible-successor bridge on the repaired
visible-avoid query surface. Once the translated instantiated RHS item is
present on LeaTTa's executable `queryOp` surface, the avoid-aware HE
`equation_match` successor is already visible up to α-equivalence on the
no-variable-values fragment. -/
theorem queryOp_contains_equation_match_visible_successor_of_instantiated_item_againstVisible
    {space : Space} {src rhs : Atom} {qb : Bindings} {fuel : Nat}
    {gt : Metta.GroundingTable}
    (prev : Metta.Minimal.Stack) (counter : Nat)
    (hquery : (rhs, qb) ∈ queryEquationsAgainstVisible space src fuel)
    (heq : qb.equalities = [])
    (hfresh : ValueKeysFreshForValues (toLeaTTaMatchBindings qb))
    (hdepth : atomDepth rhs + 2 ≤ fuel)
    (hitem :
      Metta.Minimal.evalResult prev
          (Metta.instantiate (toLeaTTaMatchBindings qb) (toLeaTTaAtom rhs))
          (toLeaTTaMatchBindings qb) ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (toLeaTTaAtom src) Metta.Bindings.empty).1) :
    ∃ emitted m,
      Metta.Minimal.evalResult prev emitted m ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (toLeaTTaAtom src) Metta.Bindings.empty).1 ∧
      Metta.AlphaEq emitted (toLeaTTaAtom (qb.applyFull rhs fuel)) := by
  exact
    visible_successor_of_instantiated_item
      heq (queryEquationsAgainstVisible_noVarAssignmentValues hquery)
      (queryEquationsAgainstVisible_assignmentsNodup hquery)
      hfresh hdepth hitem

/-- Typed specialization of the previous executable `queryOp` bridge: if the
translated instantiated RHS item is already present on LeaTTa's `queryOp`
surface and the translated rule/bindings satisfy LeaTTa's preservation
hypotheses, then the same `queryOp` surface already contains a visible
successor item that is both α-equivalent to the HE successor and well-typed in
LeaTTa's empty context. -/
theorem queryOp_contains_typed_equation_match_visible_successor_of_instantiated_item
    {space : Space} {src lhs rhs : Atom} {qb : Bindings} {fuel : Nat}
    {gt : Metta.GroundingTable}
    {env : Metta.TypeEnv} {Γ : List (String × Metta.Atom)} {T : Metta.Atom}
    (prev : Metta.Minimal.Stack) (counter : Nat)
    (_hquery : (rhs, qb) ∈ queryEquations space src fuel)
    (hno : NoVarAssignmentValues qb)
    (hkeys : AssignmentsNodup qb)
    (hfresh : ValueKeysFreshForValues (toLeaTTaMatchBindings qb))
    (hb : GroundBindings qb)
    (hdepth : atomDepth rhs + 2 ≤ fuel)
    (hitem :
      Metta.Minimal.evalResult prev
          (Metta.instantiate (toLeaTTaMatchBindings qb) (toLeaTTaAtom rhs))
          (toLeaTTaMatchBindings qb) ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (toLeaTTaAtom src) Metta.Bindings.empty).1)
    (hσ : Metta.Grounds env (toLeaTTaSubst qb.assignments) Γ)
    (hL : Metta.WT env Γ (toLeaTTaAtom lhs) T)
    (hR : Metta.WT env Γ (toLeaTTaAtom rhs) T) :
    ∃ emitted m,
      Metta.Minimal.evalResult prev emitted m ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (toLeaTTaAtom src) Metta.Bindings.empty).1 ∧
      Metta.AlphaEq emitted (toLeaTTaAtom (qb.applyFull rhs fuel)) ∧
      Metta.WT env [] emitted T := by
  exact
    typed_visible_successor_of_instantiated_item
      hno hkeys hfresh hb hdepth hitem hσ hL hR

/-- Typed instantiated-item bridge on the repaired visible-avoid query surface.
The same avoid-aware HE witness already yields a typed alpha-visible LeaTTa
successor once the instantiated RHS item is present on `queryOp`. -/
theorem queryOp_contains_typed_equation_match_visible_successor_of_instantiated_item_againstVisible
    {space : Space} {src lhs rhs : Atom} {qb : Bindings} {fuel : Nat}
    {gt : Metta.GroundingTable}
    {env : Metta.TypeEnv} {Γ : List (String × Metta.Atom)} {T : Metta.Atom}
    (prev : Metta.Minimal.Stack) (counter : Nat)
    (hquery : (rhs, qb) ∈ queryEquationsAgainstVisible space src fuel)
    (hfresh : ValueKeysFreshForValues (toLeaTTaMatchBindings qb))
    (hb : GroundBindings qb)
    (hdepth : atomDepth rhs + 2 ≤ fuel)
    (hitem :
      Metta.Minimal.evalResult prev
          (Metta.instantiate (toLeaTTaMatchBindings qb) (toLeaTTaAtom rhs))
          (toLeaTTaMatchBindings qb) ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (toLeaTTaAtom src) Metta.Bindings.empty).1)
    (hσ : Metta.Grounds env (toLeaTTaSubst qb.assignments) Γ)
    (hL : Metta.WT env Γ (toLeaTTaAtom lhs) T)
    (hR : Metta.WT env Γ (toLeaTTaAtom rhs) T) :
    ∃ emitted m,
      Metta.Minimal.evalResult prev emitted m ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (toLeaTTaAtom src) Metta.Bindings.empty).1 ∧
      Metta.AlphaEq emitted (toLeaTTaAtom (qb.applyFull rhs fuel)) ∧
      Metta.WT env [] emitted T := by
  exact
    typed_visible_successor_of_instantiated_item
      (queryEquationsAgainstVisible_noVarAssignmentValues hquery)
      (queryEquationsAgainstVisible_assignmentsNodup hquery)
      hfresh hb hdepth hitem hσ hL hR

/-- Typed semantic package for the executable `equation_match` seam on the
instantiated-item surface. When the translated instantiated RHS item is already
known to be present on LeaTTa's `queryOp` surface, the HE small-step and the
typed alpha-visible LeaTTa witness can be exhibited together. This is the typed
counterpart of the untyped semantic packaging above, but it stays on the
instantiated-item seam where the current preservation theorems apply directly. -/
theorem equation_match_typed_queryOp_visible_successor_of_instantiated_item
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {lhs rhs : Atom} {qb : Bindings}
    {gt : Metta.GroundingTable}
    {env : Metta.TypeEnv} {Γ : List (String × Metta.Atom)} {T : Metta.Atom}
    (prev : Metta.Minimal.Stack) (counter : Nat)
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hquery : (rhs, qb) ∈ queryEquations space (.expression es) fuel)
    (hno : NoVarAssignmentValues qb)
    (hkeys : AssignmentsNodup qb)
    (hfresh : ValueKeysFreshForValues (toLeaTTaMatchBindings qb))
    (hb : GroundBindings qb)
    (hdepth : atomDepth rhs + 2 ≤ fuel)
    (hitem :
      Metta.Minimal.evalResult prev
          (Metta.instantiate (toLeaTTaMatchBindings qb) (toLeaTTaAtom rhs))
          (toLeaTTaMatchBindings qb) ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (toLeaTTaAtom (.expression es)) Metta.Bindings.empty).1)
    (hσ : Metta.Grounds env (toLeaTTaSubst qb.assignments) Γ)
    (hL : Metta.WT env Γ (toLeaTTaAtom lhs) T)
    (hR : Metta.WT env Γ (toLeaTTaAtom rhs) T) :
    HESmallStep space d fuel (.expression es) (qb.applyFull rhs fuel) ∧
    ∃ emitted m,
      Metta.Minimal.evalResult prev emitted m ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (toLeaTTaAtom (.expression es)) Metta.Bindings.empty).1 ∧
      Metta.AlphaEq emitted (toLeaTTaAtom (qb.applyFull rhs fuel)) ∧
      Metta.WT env [] emitted T := by
  refine ⟨HESmallStep.equation_match h_not_special h_not_grounded hquery
    (NoVarAssignmentValues.hasLoop_false hno), ?_⟩
  exact
    queryOp_contains_typed_equation_match_visible_successor_of_instantiated_item
      (space := space) (src := .expression es) (lhs := lhs) (rhs := rhs)
      (qb := qb) (fuel := fuel) (gt := gt) (env := env) (Γ := Γ) (T := T)
      prev counter hquery hno hkeys hfresh hb hdepth hitem hσ hL hR

/-- True P1 simulation boundary for `HESmallStep.equation_match`: after
transporting the freshened query witness, `queryOp` should emit some concrete
LeaTTa item whose result atom is alpha-equivalent to the translated HE
successor `qb.applyFull rhs fuel`. Literal fresh names cannot be the target here:
HE freshens by rule index while LeaTTa freshens by the runtime `queryOp`
counter, so the honest positive theorem lives modulo α-renaming. We
intentionally existentialize the LeaTTa binding thread here as well; forcing it
to be literally `toLeaTTaMatchBindings qb` bakes in a fresh-name choice that
the small-step simulation itself does not need. -/
def EquationMatchVisibleItemTransport
    (space : Space) (src rhs : Atom) (qb : Bindings) (fuel : Nat)
    (gt : Metta.GroundingTable) (prev : Metta.Minimal.Stack) (counter : Nat) :
    Prop :=
  ∀ {idx lhs rawRhs k}
    (_hk : Metta.Minimal.headKey (toLeaTTaAtom src) = some k)
    (_hzip : (Atom.expression [Atom.symbol "=", lhs, rawRhs], idx) ∈ space.atoms.zipIdx)
    (_hmatch : FaithfulQueryWitness src (freshenEquation idx lhs rawRhs fuel).1 qb fuel),
    ∃ pre post emitted m,
      Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          Metta.Minimal.World.empty (toLeaTTaAtom src) =
        pre ++ (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) :: post ∧
      Metta.Minimal.evalResult prev emitted m ∈
        queryOpItemsOfRule prev (toLeaTTaAtom src) Metta.Bindings.empty (counter + pre.length)
          (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) ∧
      Metta.AlphaEq emitted (toLeaTTaAtom (qb.applyFull rhs fuel))

/-- Honest positive simulation theorem at the visible-successor item layer.
Once the specialized freshened-witness transport above is discharged, LeaTTa's
executable `queryOp` surface already contains an item whose emitted atom is the
translated HE `equation_match` successor up to α-renaming. This is the theorem
the eventual `HESmallStep.equation_match` bridge should consume. -/
theorem queryOp_contains_equation_match_visible_successor_of_transport
    {space : Space} {src rhs : Atom} {qb : Bindings} {fuel : Nat}
    {gt : Metta.GroundingTable} {k : String}
    (prev : Metta.Minimal.Stack) (counter : Nat)
    (hk : Metta.Minimal.headKey (toLeaTTaAtom src) = some k)
    (hquery : (rhs, qb) ∈ queryEquations space src fuel)
    (htransport : EquationMatchVisibleItemTransport
      space src rhs qb fuel gt prev counter) :
    ∃ emitted m,
      Metta.Minimal.evalResult prev emitted m ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (toLeaTTaAtom src) Metta.Bindings.empty).1 ∧
      Metta.AlphaEq emitted (toLeaTTaAtom (qb.applyFull rhs fuel)) := by
  let env := Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt
  let st0 : Metta.Minimal.St := { counter := counter, world := Metta.Minimal.World.empty }
  obtain ⟨idx, lhs, rawRhs, hzip, _hrule, hmatch⟩ :=
    queryEquations_extractRule_witness hquery
  obtain ⟨pre, post, emitted, m, hsplit, hitem, halpha⟩ := htransport hk hzip hmatch
  have hNotVarHead : Metta.Minimal.isVariableHeaded (toLeaTTaAtom src) = false := by
    rcases Metta.headKey_some hk with hsrc | ⟨ls, hsrc⟩
    · rw [hsrc]
      simp [Metta.Minimal.isVariableHeaded]
    · rw [hsrc]
      simp [Metta.Minimal.isVariableHeaded]
  refine ⟨emitted, m, ?_, halpha⟩
  exact
    queryOp_contains_item_of_splitCandidate env st0 prev
      (toLeaTTaAtom src) Metta.Bindings.empty hNotVarHead hsplit hitem

/-- Avoid-aware counterpart of `EquationMatchVisibleItemTransport`.

The raw rule/candidate layer is still LeaTTa's unrenamed equation rule, but the
HE witness consumed by the transport comes from `freshenEquationAgainst`, whose
avoid set is the variables already visible in the query atom. This is the
single named hypothesis needed by repaired query-surface bridge theorems. -/
def EquationMatchVisibleItemTransportAgainst
    (space : Space) (src rhs : Atom) (qb : Bindings) (fuel : Nat)
    (gt : Metta.GroundingTable) (prev : Metta.Minimal.Stack) (counter : Nat) :
    Prop :=
  ∀ {idx lhs rawRhs k}
    (_hk : Metta.Minimal.headKey (toLeaTTaAtom src) = some k)
    (_hzip : (Atom.expression [Atom.symbol "=", lhs, rawRhs], idx) ∈ space.atoms.zipIdx)
    (_hmatch : FaithfulQueryWitness src
      (freshenEquationAgainst ((collectVars src fuel).eraseDups) idx lhs rawRhs fuel).1
      qb fuel),
    ∃ pre post emitted m,
      Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          Metta.Minimal.World.empty (toLeaTTaAtom src) =
        pre ++ (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) :: post ∧
      Metta.Minimal.evalResult prev emitted m ∈
        queryOpItemsOfRule prev (toLeaTTaAtom src) Metta.Bindings.empty (counter + pre.length)
          (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) ∧
      Metta.AlphaEq emitted (toLeaTTaAtom (qb.applyFull rhs fuel))

/-- Constructor for the common equality-bearing visible transport case where HE's
successor remains a variable and LeaTTa's executable item emits a variable. The
premises are deliberately lower-level than `EquationMatchVisibleItemTransportAgainst`:
they provide the concrete candidate split, the concrete `queryOpItemsOfRule`
membership, and the HE unresolved-variable successor. This theorem supplies only
the alpha-equivalence step between the two variable names. -/
theorem equationMatchVisibleItemTransportAgainst_of_variable_item
    {space : Space} {src rhs : Atom} {qb : Bindings} {fuel : Nat}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack} {counter : Nat}
    (h :
      ∀ {idx lhs rawRhs k}
        (_hk : Metta.Minimal.headKey (toLeaTTaAtom src) = some k)
        (_hzip : (Atom.expression [Atom.symbol "=", lhs, rawRhs], idx) ∈ space.atoms.zipIdx)
        (_hmatch : FaithfulQueryWitness src
          (freshenEquationAgainst ((collectVars src fuel).eraseDups) idx lhs rawRhs fuel).1
          qb fuel),
        ∃ pre post emittedVar targetVar m,
          Metta.Minimal.candidatesW
              (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
              Metta.Minimal.World.empty (toLeaTTaAtom src) =
            pre ++ (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) :: post ∧
          qb.applyFull rhs fuel = .var targetVar ∧
          Metta.Minimal.evalResult prev (Metta.Atom.var emittedVar) m ∈
            queryOpItemsOfRule prev (toLeaTTaAtom src) Metta.Bindings.empty
              (counter + pre.length) (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs)) :
    EquationMatchVisibleItemTransportAgainst space src rhs qb fuel gt prev counter := by
  intro idx lhs rawRhs k hk hzip hmatch
  obtain ⟨pre, post, emittedVar, targetVar, m, hsplit, happly, hitem⟩ :=
    h hk hzip hmatch
  refine ⟨pre, post, Metta.Atom.var emittedVar, m, hsplit, hitem, ?_⟩
  rw [happly]
  simpa [toLeaTTaAtom] using alphaEq_var_var emittedVar targetVar

/-- Honest positive simulation theorem for the repaired visible-avoid
`queryEquationsAgainstVisible` surface. Once the avoid-aware transport witness
is supplied, LeaTTa's executable `queryOp` surface already contains an emitted
item alpha-equivalent to the HE visible successor. -/
theorem queryOp_contains_equation_match_visible_successor_againstVisible_of_transport
    {space : Space} {src rhs : Atom} {qb : Bindings} {fuel : Nat}
    {gt : Metta.GroundingTable} {k : String}
    (prev : Metta.Minimal.Stack) (counter : Nat)
    (hk : Metta.Minimal.headKey (toLeaTTaAtom src) = some k)
    (hquery : (rhs, qb) ∈ queryEquationsAgainstVisible space src fuel)
    (htransport : EquationMatchVisibleItemTransportAgainst
      space src rhs qb fuel gt prev counter) :
    ∃ emitted m,
      Metta.Minimal.evalResult prev emitted m ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (toLeaTTaAtom src) Metta.Bindings.empty).1 ∧
      Metta.AlphaEq emitted (toLeaTTaAtom (qb.applyFull rhs fuel)) := by
  let env := Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt
  let st0 : Metta.Minimal.St := { counter := counter, world := Metta.Minimal.World.empty }
  obtain ⟨idx, lhs, rawRhs, hzip, _hrule, hmatch⟩ :=
    queryEquationsAgainstVisible_extractRule_witness hquery
  obtain ⟨pre, post, emitted, m, hsplit, hitem, halpha⟩ := htransport hk hzip hmatch
  have hNotVarHead : Metta.Minimal.isVariableHeaded (toLeaTTaAtom src) = false := by
    rcases Metta.headKey_some hk with hsrc | ⟨ls, hsrc⟩
    · rw [hsrc]
      simp [Metta.Minimal.isVariableHeaded]
    · rw [hsrc]
      simp [Metta.Minimal.isVariableHeaded]
  refine ⟨emitted, m, ?_, halpha⟩
  exact
    queryOp_contains_item_of_splitCandidate env st0 prev
      (toLeaTTaAtom src) Metta.Bindings.empty hNotVarHead hsplit hitem

/-- Downstream package for the repaired visible-avoid query surface: the public
HE query witness has already passed the loop filter, and under the avoid-aware
transport obligation the corresponding LeaTTa executable `queryOp` item is
visible up to alpha-equivalence. -/
theorem queryEquationsAgainstVisible_queryOp_visible_successor_package_of_transport
    {space : Space} {src rhs : Atom} {qb : Bindings} {fuel : Nat}
    {gt : Metta.GroundingTable} {k : String}
    (prev : Metta.Minimal.Stack) (counter : Nat)
    (hk : Metta.Minimal.headKey (toLeaTTaAtom src) = some k)
    (hquery : (rhs, qb) ∈ queryEquationsAgainstVisible space src fuel)
    (htransport : EquationMatchVisibleItemTransportAgainst
      space src rhs qb fuel gt prev counter) :
    qb.hasLoop = false ∧
    ∃ emitted m,
      Metta.Minimal.evalResult prev emitted m ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (toLeaTTaAtom src) Metta.Bindings.empty).1 ∧
      Metta.AlphaEq emitted (toLeaTTaAtom (qb.applyFull rhs fuel)) := by
  refine ⟨queryEquationsAgainstVisible_hasLoop_false hquery, ?_⟩
  exact
    queryOp_contains_equation_match_visible_successor_againstVisible_of_transport
      (space := space) (src := src) (rhs := rhs) (qb := qb)
      (fuel := fuel) (gt := gt) (k := k)
      prev counter hk hquery htransport

/-- Repaired HE-side equation-step package for the visible-avoid surface. Under
the same avoid-aware transport obligation used by the executable bridge, we can
exhibit both the HE companion equation step and the corresponding LeaTTa
`queryOp` witness up to alpha-equivalence. -/
theorem equation_match_againstVisible_queryOp_visible_successor_package_of_transport
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs : Atom} {qb : Bindings}
    {gt : Metta.GroundingTable} {k : String}
    (prev : Metta.Minimal.Stack) (counter : Nat)
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey (toLeaTTaAtom (.expression es)) = some k)
    (h_query : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    (htransport : EquationMatchVisibleItemTransportAgainst
      space (.expression es) rhs qb fuel gt prev counter) :
    HEEquationStepAgainstVisible space d fuel (.expression es) (qb.applyFull rhs fuel) ∧
    ∃ emitted m,
      Metta.Minimal.evalResult prev emitted m ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (toLeaTTaAtom (.expression es)) Metta.Bindings.empty).1 ∧
      Metta.AlphaEq emitted (toLeaTTaAtom (qb.applyFull rhs fuel)) := by
  refine
    ⟨HEEquationStepAgainstVisible.equation_match
        h_not_special h_not_grounded h_query
        (queryEquationsAgainstVisible_hasLoop_false h_query),
      ?_⟩
  exact
    queryOp_contains_equation_match_visible_successor_againstVisible_of_transport
      (space := space) (src := .expression es) (rhs := rhs) (qb := qb)
      (fuel := fuel) (gt := gt) (k := k)
      prev counter hk h_query htransport

/-- Concrete executable-side `queryOp` hit for an HE equation successor.  This
contains only the LeaTTa observation evidence: some emitted runtime item is in
the `queryOp` result list and is alpha-equivalent to the translated HE
successor. -/
def LeaTTaEquationQueryOpHit
    (space : Space) (_fuel : Nat) (src dst : Atom)
    (gt : Metta.GroundingTable) (prev : Metta.Minimal.Stack)
    (counter : Nat) : Prop :=
  ∃ emitted bindings,
    Metta.Minimal.evalResult prev emitted bindings ∈
      (Metta.Minimal.queryOp
        (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
        { counter := counter, world := Metta.Minimal.World.empty }
        prev (toLeaTTaAtom src) Metta.Bindings.empty).1 ∧
    Metta.AlphaEq emitted (toLeaTTaAtom dst)

/-- Local freshened-item transport obligation for the repaired visible-query
surface.  The HE query witness already determines the raw candidate split; this
predicate isolates the remaining executable content at the single-candidate
level: LeaTTa freshening, matcher output, merge, loop filtering, instantiation,
and alpha-agreement with the HE visible successor. -/
def FreshenedQueryOpItemTransportAgainstVisible
    (space : Space) (src rhs : Atom) (qb : Bindings) (fuel : Nat)
    (gt : Metta.GroundingTable) (prev : Metta.Minimal.Stack) (counter : Nat) :
    Prop :=
  ∀ {idx lhs rawRhs pre post k}
    (_hk : Metta.Minimal.headKey (toLeaTTaAtom src) = some k)
    (_hzip : (Atom.expression [Atom.symbol "=", lhs, rawRhs], idx) ∈ space.atoms.zipIdx)
    (_hmatch : FaithfulQueryWitness src
      (freshenEquationAgainst ((collectVars src fuel).eraseDups) idx lhs rawRhs fuel).1
      qb fuel)
    (_hsplit :
      Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          Metta.Minimal.World.empty (toLeaTTaAtom src) =
        pre ++ (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) :: post),
    ∃ freshLhs freshRhs mb m emitted,
      (Metta.Minimal.freshenRuleAvoiding (counter + pre.length)
          (Metta.Minimal.queryOpAvoid prev (toLeaTTaAtom src) Metta.Bindings.empty)
          (toLeaTTaAtom lhs) (toLeaTTaAtom rawRhs)).1 =
        (freshLhs, freshRhs) ∧
      mb ∈ Metta.matchAtoms freshLhs (toLeaTTaAtom src) ∧
      m ∈ Metta.Bindings.merge Metta.Bindings.empty mb ∧
      Metta.Bindings.hasLoop m = false ∧
      emitted = Metta.instantiate m freshRhs ∧
      Metta.AlphaEq emitted (toLeaTTaAtom (qb.applyFull rhs fuel))

/-- Variable-successor specialization of the local freshened-item transport
obligation.  It records the executable single-candidate facts and leaves the
alpha-agreement to the generic variable/variable alpha-equivalence lemma. -/
def FreshenedVariableQueryOpItemTransportAgainstVisible
    (space : Space) (src rhs : Atom) (qb : Bindings) (fuel : Nat)
    (gt : Metta.GroundingTable) (prev : Metta.Minimal.Stack) (counter : Nat) :
    Prop :=
  ∀ {idx lhs rawRhs pre post k}
    (_hk : Metta.Minimal.headKey (toLeaTTaAtom src) = some k)
    (_hzip : (Atom.expression [Atom.symbol "=", lhs, rawRhs], idx) ∈ space.atoms.zipIdx)
    (_hmatch : FaithfulQueryWitness src
      (freshenEquationAgainst ((collectVars src fuel).eraseDups) idx lhs rawRhs fuel).1
      qb fuel)
    (_hsplit :
      Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          Metta.Minimal.World.empty (toLeaTTaAtom src) =
        pre ++ (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) :: post),
    ∃ freshLhs freshRhs mb m emittedVar targetVar,
      (Metta.Minimal.freshenRuleAvoiding (counter + pre.length)
          (Metta.Minimal.queryOpAvoid prev (toLeaTTaAtom src) Metta.Bindings.empty)
          (toLeaTTaAtom lhs) (toLeaTTaAtom rawRhs)).1 =
        (freshLhs, freshRhs) ∧
      mb ∈ Metta.matchAtoms freshLhs (toLeaTTaAtom src) ∧
      m ∈ Metta.Bindings.merge Metta.Bindings.empty mb ∧
      Metta.Bindings.hasLoop m = false ∧
      Metta.instantiate m freshRhs = Metta.Atom.var emittedVar ∧
      qb.applyFull rhs fuel = .var targetVar

/-- A variable-emitting local item is enough for the full freshened-item
transport when the HE visible successor is also a variable. -/
theorem freshenedQueryOpItemTransportAgainstVisible_of_variable_item
    {space : Space} {src rhs : Atom} {qb : Bindings} {fuel : Nat}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack} {counter : Nat}
    (hvar : FreshenedVariableQueryOpItemTransportAgainstVisible
      space src rhs qb fuel gt prev counter) :
    FreshenedQueryOpItemTransportAgainstVisible
      space src rhs qb fuel gt prev counter := by
  intro idx lhs rawRhs pre post k hk hzip hmatch hsplit
  obtain
    ⟨freshLhs, freshRhs, mb, m, emittedVar, targetVar,
      hfresh, hmb, hmerge, hloop, hemitted, happly⟩ :=
    hvar hk hzip hmatch hsplit
  refine
    ⟨freshLhs, freshRhs, mb, m, Metta.Atom.var emittedVar,
      hfresh, hmb, hmerge, hloop, ?_, ?_⟩
  · exact hemitted.symm
  · rw [happly]
    simpa [toLeaTTaAtom] using alphaEq_var_var emittedVar targetVar

/-- Candidate extraction plus a local freshened-item transport proof produces
the concrete executable `queryOp` witness for the repaired visible-query
surface.  This removes candidate selection from the remaining bridge debt: the
only supplied hypothesis is now the single-candidate LeaTTa matcher/freshening
transport. -/
theorem queryOp_contains_equation_match_visible_successor_againstVisible_of_freshened_item_transport
    {space : Space} {src rhs : Atom} {qb : Bindings} {fuel : Nat}
    {gt : Metta.GroundingTable} {k : String}
    (prev : Metta.Minimal.Stack) (counter : Nat)
    (hk : Metta.Minimal.headKey (toLeaTTaAtom src) = some k)
    (hquery : (rhs, qb) ∈ queryEquationsAgainstVisible space src fuel)
    (hitemTransport : FreshenedQueryOpItemTransportAgainstVisible
      space src rhs qb fuel gt prev counter) :
    ∃ emitted m,
      Metta.Minimal.evalResult prev emitted m ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (toLeaTTaAtom src) Metta.Bindings.empty).1 ∧
      Metta.AlphaEq emitted (toLeaTTaAtom (qb.applyFull rhs fuel)) := by
  let env := Metta.Minimal.MinEnv.ofAtomsGT (toLeaTTaAtoms space.atoms) gt
  let st0 : Metta.Minimal.St := { counter := counter, world := Metta.Minimal.World.empty }
  obtain ⟨idx, lhs, rawRhs, pre, post, hzip, hmatch, hsplit⟩ :=
    queryEquationsAgainstVisible_extractCandidate_split
      (space := space) (src := src) (rhs := rhs) (qb := qb)
      (fuel := fuel) (gt := gt) (k := k) hk hquery
  obtain
    ⟨freshLhs, freshRhs, mb, m, emitted, hfresh, hmb, hmerge,
      hloop, hemitted, halpha⟩ :=
    hitemTransport hk hzip hmatch hsplit
  have hitem :
      Metta.Minimal.evalResult prev emitted m ∈
        queryOpItemsOfRule prev (toLeaTTaAtom src) Metta.Bindings.empty
          (counter + pre.length) (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs) := by
    refine
      (mem_queryOpItemsOfRule_iff
        prev (toLeaTTaAtom src) Metta.Bindings.empty
        (counter + pre.length) (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs)
        (Metta.Minimal.evalResult prev emitted m)).2 ?_
    refine ⟨mb, ?_, m, hmerge, hloop, ?_⟩
    · simpa [hfresh] using hmb
    · rw [hfresh, hemitted]
  have hNotVarHead : Metta.Minimal.isVariableHeaded (toLeaTTaAtom src) = false := by
    rcases Metta.headKey_some hk with hsrc | ⟨ls, hsrc⟩
    · rw [hsrc]
      simp [Metta.Minimal.isVariableHeaded]
    · rw [hsrc]
      simp [Metta.Minimal.isVariableHeaded]
  refine ⟨emitted, m, ?_, halpha⟩
  exact
    queryOp_contains_item_of_splitCandidate env st0 prev
      (toLeaTTaAtom src) Metta.Bindings.empty hNotVarHead hsplit hitem

/-- Direct `LeaTTaEquationQueryOpHit` constructor from the smaller local
freshened-item transport obligation. -/
theorem leattaEquationQueryOpHit_of_freshened_item_transport_againstVisible
    {space : Space} {src rhs : Atom} {qb : Bindings} {fuel : Nat}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String}
    (hk : Metta.Minimal.headKey (toLeaTTaAtom src) = some k)
    (hquery : (rhs, qb) ∈ queryEquationsAgainstVisible space src fuel)
    (hitemTransport : FreshenedQueryOpItemTransportAgainstVisible
      space src rhs qb fuel gt prev counter) :
    LeaTTaEquationQueryOpHit
      space fuel src (qb.applyFull rhs fuel) gt prev counter := by
  simpa [LeaTTaEquationQueryOpHit] using
    queryOp_contains_equation_match_visible_successor_againstVisible_of_freshened_item_transport
      (space := space) (src := src) (rhs := rhs) (qb := qb)
      (fuel := fuel) (gt := gt) (k := k)
      prev counter hk hquery hitemTransport

/-- Direct executable-hit constructor for the variable-successor specialization
of the repaired visible-query transport. -/
theorem leattaEquationQueryOpHit_of_freshened_variable_item_transport_againstVisible
    {space : Space} {src rhs : Atom} {qb : Bindings} {fuel : Nat}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String}
    (hk : Metta.Minimal.headKey (toLeaTTaAtom src) = some k)
    (hquery : (rhs, qb) ∈ queryEquationsAgainstVisible space src fuel)
    (hvarTransport : FreshenedVariableQueryOpItemTransportAgainstVisible
      space src rhs qb fuel gt prev counter) :
    LeaTTaEquationQueryOpHit
      space fuel src (qb.applyFull rhs fuel) gt prev counter := by
  exact
    leattaEquationQueryOpHit_of_freshened_item_transport_againstVisible
      (space := space) (src := src) (rhs := rhs) (qb := qb)
      (fuel := fuel) (gt := gt) (prev := prev) (counter := counter)
      (k := k) hk hquery
      (freshenedQueryOpItemTransportAgainstVisible_of_variable_item hvarTransport)

/-- The local freshened-item transport predicate subsumes the older
raw-candidate transport certificate. Candidate selection is reconstructed from
the raw HE rule witness; the remaining executable content comes from the local
single-candidate transport obligation. -/
theorem equationMatchVisibleItemTransportAgainst_of_freshened_item_transport
    {space : Space} {src rhs : Atom} {qb : Bindings} {fuel : Nat}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat}
    (hitemTransport : FreshenedQueryOpItemTransportAgainstVisible
      space src rhs qb fuel gt prev counter) :
    EquationMatchVisibleItemTransportAgainst
      space src rhs qb fuel gt prev counter := by
  intro idx lhs rawRhs k hk hzip hmatch
  obtain ⟨pre, post, hsplit⟩ :=
    candidate_split_of_againstVisible_witness
      (space := space) (src := src) (lhs := lhs) (rawRhs := rawRhs)
      (qb := qb) (fuel := fuel) (gt := gt) (idx := idx) (k := k)
      hk hzip hmatch
  obtain ⟨freshLhs, freshRhs, mb, m, emitted, hfresh, hmb, hmerge,
      hloop, hemitted, halpha⟩ :=
    hitemTransport hk hzip hmatch hsplit
  refine ⟨pre, post, emitted, m, hsplit, ?_, halpha⟩
  refine
    (mem_queryOpItemsOfRule_iff
      prev (toLeaTTaAtom src) Metta.Bindings.empty
      (counter + pre.length) (toLeaTTaAtom lhs, toLeaTTaAtom rawRhs)
      (Metta.Minimal.evalResult prev emitted m)).2 ?_
  refine ⟨mb, ?_, m, hmerge, hloop, ?_⟩
  · simpa [hfresh] using hmb
  · rw [hfresh, hemitted]

/-- Any repaired avoid-aware transport certificate produces the concrete
`queryOp` hit consumed by the executable-trace boundary. -/
theorem leattaEquationQueryOpHit_of_transport_againstVisible
    {space : Space} {src rhs : Atom} {qb : Bindings} {fuel : Nat}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String}
    (hk : Metta.Minimal.headKey (toLeaTTaAtom src) = some k)
    (hquery : (rhs, qb) ∈ queryEquationsAgainstVisible space src fuel)
    (htransport : EquationMatchVisibleItemTransportAgainst
      space src rhs qb fuel gt prev counter) :
    LeaTTaEquationQueryOpHit
      space fuel src (qb.applyFull rhs fuel) gt prev counter := by
  simpa [LeaTTaEquationQueryOpHit] using
    queryOp_contains_equation_match_visible_successor_againstVisible_of_transport
      (space := space) (src := src) (rhs := rhs) (qb := qb)
      (fuel := fuel) (gt := gt) (k := k)
      prev counter hk hquery htransport

end Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
