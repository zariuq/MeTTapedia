import Mettapedia.Languages.MeTTa.HE.MatcherBridge
import MettaHyperonFull.Minimal.Interpreter
import MettaHyperonFull.Operational.Properties
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

/-- HE assignment-key uniqueness, stated explicitly so bridge lemmas can use it
without reaching into private helper files. -/
def AssignmentsNodup (b : Bindings) : Prop :=
  (b.assignments.map Prod.fst).Nodup

@[simp] theorem toLeaTTaAtoms_nil :
    toLeaTTaAtoms [] = [] := rfl

@[simp] theorem toLeaTTaAtoms_cons (a : Atom) (as : List Atom) :
    toLeaTTaAtoms (a :: as) = toLeaTTaAtom a :: toLeaTTaAtoms as := rfl

@[simp] theorem toLeaTTaSubst_nil :
    toLeaTTaSubst [] = [] := rfl

@[simp] theorem toLeaTTaSubst_cons (v : String) (a : Atom) (rest : List (String × Atom)) :
    toLeaTTaSubst ((v, a) :: rest) =
      Metta.Subst.extend (toLeaTTaSubst rest) v (toLeaTTaAtom a) := rfl

@[simp] theorem toLeaTTaMatchSubst_nil :
    toLeaTTaMatchSubst [] = [] := rfl

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
private theorem toLeaTTaAtom_beq_self (a : Atom) :
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

private theorem lookup_some_mem_assignments {xs : List (String × Atom)}
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
    (hground : GroundAtom target)
    (hmatch : simpleMatch pattern target Bindings.empty fuel = some qb) :
    AssignmentsNodup qb :=
  (simpleMatch_groundCanon fuel).1 pattern target Bindings.empty qb
    GroundBindings.empty AssignmentsNodup.empty hground hmatch |>.2

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

/-- Viewing a LeaTTa substitution as `Bindings` and projecting it back to a
substitution is definitionally lossless. -/
@[simp] theorem bindingsToSubst_ofSubst (s : Metta.Subst) :
    Metta.bindingsToSubst (Metta.Bindings.ofSubst s) = s := by
  induction s with
  | nil =>
      rfl
  | cons p s ih =>
      rcases p with ⟨x, a⟩
      simpa [Metta.Bindings.ofSubst, Metta.bindingsToSubst] using
        congrArg (fun t => (x, a) :: t) ih

@[simp] theorem lookupVal_ofSubst (s : Metta.Subst) (v : String) :
    Metta.Bindings.lookupVal (Metta.Bindings.ofSubst s) v = Metta.Subst.lookup s v := by
  induction s with
  | nil =>
      rfl
  | cons p s ih =>
      rcases p with ⟨x, a⟩
      cases hbx : (v == x) with
      | true =>
          simp [Metta.Bindings.ofSubst, Metta.Bindings.lookupVal, Metta.Subst.lookup, hbx]
      | false =>
          simpa [Metta.Bindings.ofSubst, Metta.Bindings.lookupVal, Metta.Subst.lookup, hbx] using ih

/-- Direct value lookup through the translated LeaTTa assignment bindings
coincides with translated HE lookup. -/
@[simp] theorem toLeaTTaAssignmentBindings_lookupVal (b : Bindings) (v : String) :
    Metta.Bindings.lookupVal (toLeaTTaAssignmentBindings b) v =
      Option.map toLeaTTaAtom (b.lookup v) := by
  simp [toLeaTTaAssignmentBindings, lookupVal_ofSubst, Bindings.lookup, toLeaTTaSubst_lookup]

/-- On HE bindings with unique assignment keys, the matcher-oriented LeaTTa
binding order has the same direct lookup behavior as the substitution-oriented
translation. This is the exact extensional bridge needed for transporting HE
matcher witnesses into LeaTTa matcher witnesses without losing substitution
meaning. -/
private def LeaLookupExt (b : Bindings) (lb : Metta.Bindings) : Prop :=
  ∀ v, Metta.Bindings.lookupVal lb v = Option.map toLeaTTaAtom (b.lookup v)

@[simp] theorem toLeaTTaMatchBindings_lookupVal_of_nodup
    {b : Bindings} (hkeys : AssignmentsNodup b) (v : String) :
    Metta.Bindings.lookupVal (toLeaTTaMatchBindings b) v =
      Option.map toLeaTTaAtom (b.lookup v) := by
  unfold AssignmentsNodup at hkeys
  unfold toLeaTTaMatchBindings
  simp [lookupVal_ofSubst, Bindings.lookup, toLeaTTaMatchSubst_lookup,
    lookup_reverse_eq_of_assignmentKeysNodup hkeys]

@[simp] theorem LeaLookupExt.empty :
    LeaLookupExt Bindings.empty Metta.Bindings.empty := by
  intro v
  simp [Bindings.empty, Bindings.lookup, Metta.Bindings.empty, Metta.Bindings.lookupVal]

theorem LeaLookupExt.of_nodup {b : Bindings} (hkeys : AssignmentsNodup b) :
    LeaLookupExt b (toLeaTTaMatchBindings b) := by
  intro v
  exact toLeaTTaMatchBindings_lookupVal_of_nodup hkeys v

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

private theorem LeaLookupExt.addValRaw_of_lookup_none
    {b : Bindings} {lb : Metta.Bindings} {v : String} {val : Atom}
    (hseed : LeaLookupExt b lb) (h : b.lookup v = none) :
    LeaLookupExt (b.assign v val) (Metta.Bindings.addValRaw lb v (toLeaTTaAtom val)) := by
  intro w
  by_cases hw : w = v
  · subst w
    have hassign : (b.assign v val).lookup v = some val :=
      lookup_assign_of_lookup_none b v val h
    simp [hassign]
  · rw [lookupVal_addValRaw_of_ne lb (a := toLeaTTaAtom val) hw,
      assign_lookup_ne b v val w hw h]
    exact hseed w

private theorem LeaLookupExt.refl_of_lookup_some_eq
    {b : Bindings} {lb : Metta.Bindings} {v : String} {val : Atom}
    (hseed : LeaLookupExt b lb) (_h : b.lookup v = some val) :
    LeaLookupExt b lb := hseed

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
                  (Metta.matchAtomsWith none x y).flatMap fun mb =>
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
  have hseeded :
      qb ∈ Metta.matchAll none
        ((Metta.matchAtomsWith none x y).flatMap
          (fun mb => Metta.Bindings.merge b mb)) xs ys := by
    rw [matchAll_seedwise xs ys
      ((Metta.matchAtomsWith none x y).flatMap
        (fun mb => Metta.Bindings.merge b mb))]
    exact List.mem_flatMap.mpr ⟨b', hhead, htail⟩
  simpa [Metta.matchAll, Metta.matchAtoms] using hseeded

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

/-- Projecting a LeaTTa binding set to a substitution preserves direct value
lookup exactly: `bindingsToSubst` drops only equality relations, and
`lookupVal` ignores them already. -/
@[simp] private theorem subst_lookup_bindingsToSubst
    (bs : Metta.Bindings) (v : String) :
    Metta.Subst.lookup (Metta.bindingsToSubst bs) v =
      Metta.Bindings.lookupVal bs v := by
  induction bs with
  | nil =>
      rfl
  | cons r rs ih =>
      cases r with
      | val x a =>
          cases hbx : (v == x) with
          | true =>
              simp [Metta.bindingsToSubst, Metta.Subst.lookup, Metta.Bindings.lookupVal, hbx]
          | false =>
              simpa [Metta.bindingsToSubst, Metta.Subst.lookup, Metta.Bindings.lookupVal, hbx] using ih
      | eq x y =>
          simpa [Metta.bindingsToSubst, Metta.Bindings.lookupVal] using ih

/-- LeaTTa instantiation depends only on direct `lookupVal` behavior, not on the
concrete order of the binding list. This is the extensionality principle the
equation-step witness transport will use after decomposing singleton-seeded
`matchAll` results. -/
private theorem instantiate_eq_of_lookupVal_eq
    {bs₁ bs₂ : Metta.Bindings}
    (hlookup : ∀ v, Metta.Bindings.lookupVal bs₁ v = Metta.Bindings.lookupVal bs₂ v) :
    ∀ a : Metta.Atom, Metta.instantiate bs₁ a = Metta.instantiate bs₂ a := by
  intro a
  unfold Metta.instantiate
  induction a with
  | var x =>
      simp [Metta.Subst.apply, subst_lookup_bindingsToSubst, hlookup x]
  | expr xs ih =>
      simp only [Metta.Subst.apply]
      congr 1
      exact List.map_congr_left ih
  | _ =>
      simp [Metta.Subst.apply]

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

@[simp] private theorem merge_empty_right (lb : Metta.Bindings) :
    Metta.Bindings.merge lb [] = [lb] := by
  simp [Metta.Bindings.merge]

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

private theorem simpleMatch_var_seeded_lookup_bridge_of_ne_self
    {target : Atom} {b qb : Bindings} {lb : Metta.Bindings} {v : String} {fuel : Nat}
    (_hkeys : AssignmentsNodup b) (hseed : LeaLookupExt b lb)
    (hnotself : target ≠ .var v)
    (hmatch : simpleMatch (.var v) target b fuel = some qb) :
    ∃ lb',
      lb' ∈ (Metta.matchAtoms (.var v) (toLeaTTaAtom target)).flatMap
        (fun mb => Metta.Bindings.merge lb mb) ∧
      LeaLookupExt qb lb' := by
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
              have hlbnone : Metta.Bindings.lookupVal lb v = none := by
                simpa [hlook] using hseed v
              refine ⟨Metta.Bindings.addValRaw lb v (Metta.Atom.expr (toLeaTTaAtoms es)), ?_, ?_⟩
              · refine List.mem_flatMap.mpr ?_
                refine ⟨[Metta.BindingRel.val v (Metta.Atom.expr (toLeaTTaAtoms es))], ?_, ?_⟩
                · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom]
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
                have hlb : Metta.Bindings.lookupVal lb v = some (Metta.Atom.expr (toLeaTTaAtoms es)) := by
                  simpa [hlook, toLeaTTaAtom] using hseed v
                refine ⟨lb, ?_, hseed⟩
                refine List.mem_flatMap.mpr ?_
                refine ⟨[Metta.BindingRel.val v (Metta.Atom.expr (toLeaTTaAtoms es))], ?_, ?_⟩
                · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom]
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
                  (Metta.Atom.gnd (toLeaTTaGround g) == Metta.Atom.gnd (toLeaTTaGround g)) = true := by
                  simpa [toLeaTTaAtom] using toLeaTTaAtom_beq_self (.grounded g)
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

@[simp] theorem instantiate_toLeaTTaAssignmentBindings (b : Bindings) (a : Metta.Atom) :
    Metta.instantiate (toLeaTTaAssignmentBindings b) a =
      Metta.Subst.apply (toLeaTTaSubst b.assignments) a := by
  simp [Metta.instantiate, toLeaTTaAssignmentBindings]

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
    {b : Bindings} (hkeys : AssignmentsNodup b) (a : Atom) :
    Metta.instantiate (toLeaTTaMatchBindings b) (toLeaTTaAtom a) =
      Metta.Subst.apply (toLeaTTaSubst b.assignments) (toLeaTTaAtom a) := by
  unfold toLeaTTaMatchBindings
  simp [Metta.instantiate]
  apply subst_apply_eq_of_lookup_eq
  exact matchSubst_lookup_eq_subst_of_nodup (by simpa [AssignmentsNodup] using hkeys)

/-- On the no-variable-values fragment, HE's recursive `resolve` agrees with a
single direct lookup as soon as it has at least one unfold step available. -/
@[simp] theorem resolve_eq_lookup_of_noVarAssignmentValues {b : Bindings}
    (hno : NoVarAssignmentValues b) (v : String) (fuel : Nat) :
    b.resolve v (fuel + 1) = b.lookup v := by
  simp [Bindings.resolve]
  cases h : b.lookup v with
  | none =>
      simp
  | some a =>
      cases a with
      | symbol s =>
          simp
      | var x =>
          exact False.elim (hno h)
      | grounded g =>
          simp
      | expression es =>
          simp

/-- First substitution correspondence lemma: on variable leaves, HE's
assignment-only application surface matches LeaTTa instantiation once we are in
the no-variable-values fragment. This is the kernel of the later ground-query
equation-step bridge. -/
theorem toLeaTTaAtom_apply_var_eq_instantiate {b : Bindings}
    (hno : NoVarAssignmentValues b) (v : String) (fuel : Nat) :
    toLeaTTaAtom (b.apply (.var v) (fuel + 2)) =
      Metta.instantiate (toLeaTTaAssignmentBindings b) (.var v) := by
  rw [instantiate_toLeaTTaAssignmentBindings]
  simp [Bindings.apply]
  rw [resolve_eq_lookup_of_noVarAssignmentValues hno v fuel]
  simp [Metta.Subst.apply, toLeaTTaSubst_lookup]
  change toLeaTTaAtom (match b.lookup v with
      | some val => val
      | none => Atom.var v) =
    (Option.map toLeaTTaAtom (b.lookup v)).getD (Metta.Atom.var v)
  cases h : b.lookup v <;> simp [toLeaTTaAtom]

/-- With enough fuel to cover the term depth, HE's bounded substitution agrees
with LeaTTa's one-pass substitution on the no-variable-values fragment. -/
theorem toLeaTTaAtom_apply_eq_subst_of_noVarAssignmentValues {b : Bindings}
    (hno : NoVarAssignmentValues b) :
    ∀ fuel a, atomDepth a + 2 ≤ fuel →
      toLeaTTaAtom (b.apply a fuel) =
        Metta.Subst.apply (toLeaTTaSubst b.assignments) (toLeaTTaAtom a) := by
  intro fuel
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
              rw [toLeaTTaAtom_apply_var_eq_instantiate hno v fuel',
                instantiate_toLeaTTaAssignmentBindings]
              simp [toLeaTTaAtom]
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
  rw [instantiate_toLeaTTaMatchBindings_eq_subst_of_nodup hkeys a]
  exact toLeaTTaAtom_apply_eq_subst_of_groundBindings hb fuel a hdepth

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
    (simpleMatch_assignmentsNodup hground hmatch)
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

private theorem mem_of_mem_zipIdx {α : Type*} {xs : List α} {x : α} {i : Nat}
    (h : (x, i) ∈ xs.zipIdx) : x ∈ xs := by
  rcases List.mem_zipIdx h with ⟨_, hi, hEq⟩
  have hi' : i < xs.length := by
    simpa using hi
  have hmem : xs[i] ∈ xs := List.getElem_mem hi'
  exact hEq.symm ▸ hmem

/-- A `queryEquations` witness comes from a specific indexed raw equation in the
space together with its freshened matcher witness. This is the precise bridge
entry point for transporting HE query evidence into LeaTTa. -/
theorem mem_queryEquations_decompose
    {space : Space} {atom rhs : Atom} {qb : Bindings} {fuel : Nat}
    (hmem : (rhs, qb) ∈ queryEquations space atom fuel) :
    ∃ eqidx ∈ space.atoms.zipIdx, ∃ lhs rawRhs,
      eqidx.1 = .expression [.symbol "=", lhs, rawRhs] ∧
      (freshenEquation eqidx.2 lhs rawRhs fuel).2 = rhs ∧
      simpleMatch (freshenEquation eqidx.2 lhs rawRhs fuel).1 atom Bindings.empty fuel = some qb := by
  rcases List.mem_filterMap.mp hmem with ⟨eqidx, heqidx, hout⟩
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
                            cases hsm : simpleMatch (freshenEquation idx lhs rawRhs fuel).1 atom Bindings.empty fuel with
                            | none =>
                                simp [hsm] at hout
                            | some b =>
                                simp [hsm] at hout
                                rcases hout with ⟨hRhs, hQb⟩
                                refine
                                  ⟨(Atom.expression [Atom.symbol "=", lhs, rawRhs], idx), heqidx,
                                    lhs, rawRhs, rfl, hRhs, ?_⟩
                                simpa [hQb] using hsm
                        | cons extra tl3 =>
                            simp at hout
              · simp [hs] at hout
          | var v =>
              simp at hout
          | grounded g =>
              simp at hout
          | expression inner =>
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

private theorem mem_toLeaTTaAtoms_of_mem {atoms : List Atom} {a : Atom}
    (h : a ∈ atoms) :
    toLeaTTaAtom a ∈ toLeaTTaAtoms atoms := by
  induction atoms with
  | nil =>
      cases h
  | cons hd tl ih =>
      simp at h ⊢
      rcases h with rfl | htl
      · exact Or.inl rfl
      · exact Or.inr (ih htl)

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
      simpleMatch (freshenEquation idx lhs rawRhs fuel).1 atom Bindings.empty fuel = some qb := by
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

end Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
