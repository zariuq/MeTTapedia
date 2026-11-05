import Mettapedia.Languages.MeTTa.PeTTa.Effects

/-!
# Closed-candidate admission for one-way data-query workers

An open stored fact can require two-way unification even when a query's
outputs are ground. A one-way worker may screen out a distinct rigid head,
but every remaining stored row must be ground. The special `cons` list view
does not justify a rigid-head screen. Missing reads are not empty domains.

This is a conservative live admission condition, not a full unifier theorem
or a native index implementation. It keeps the source-profile boundary
explicit while allowing unrelated open equation rows in a shared space.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedQueryAdmission

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (isGroundAtom Subst atomFreeVars applySubst)
open NamedSpaces SpaceSemantics

/-- Closed literal patterns are ground stored data. This also applies to
literal codec images used by finite source-query adapters. -/
theorem literal_ground {atom : Atom} (literal : Literal atom) : isGroundAtom atom = true := by
  induction literal with
  | symbol | grounded => rfl
  | expression items ordinary members ih =>
      clear ordinary members
      change isGroundAtom.isGroundList items = true
      induction items with
      | nil => rfl
      | cons first rest tail =>
          simp only [isGroundAtom.isGroundList, ih first List.mem_cons_self, Bool.true_and]
          exact tail (fun item member => ih item (List.mem_cons_of_mem _ member))

def rigidHeadClash : Atom → Atom → Bool
  | .expression (.symbol head :: _), .expression (.symbol other :: _) => head != "cons" && head != other
  | _, _ => false

theorem rigidHeadClash_blocks_match (pattern row : Atom) (bindings : Subst)
    (clash : rigidHeadClash pattern row = true) : matchValue bindings pattern row = none := by
  unfold rigidHeadClash at clash
  split at clash
  next head fields other values =>
    have different : head ≠ "cons" ∧ head ≠ other := by simpa using clash
    rw [matchValue_expression_of_not_cons bindings _ _ (by
      intro first rest same
      exact different.1 (by simpa using (List.cons.inj same).1))]
    simp only [matchValue.matchValues, matchValue_literal (.symbol head)]
    rw [if_neg (by simpa using different.2)]
    rfl
  next => cases clash

theorem rigidHeadClash_blocks_common_instance (pattern row : Atom)
    (clash : rigidHeadClash pattern row = true) (left right : Subst) :
    applySubst left pattern ≠ applySubst right row := by
  unfold rigidHeadClash at clash
  split at clash
  next head fields other values =>
    have different : head ≠ "cons" ∧ head ≠ other := by simpa using clash
    intro same
    change Atom.expression (.symbol head :: applySubst.applySubstList left fields) =
      Atom.expression (.symbol other :: applySubst.applySubstList right values) at same
    exact different.2 (Atom.symbol.inj (List.cons.inj (Atom.expression.inj same)).1)
  next => cases clash

def rowReady (pattern row : Atom) : Bool := isGroundAtom row || rigidHeadClash pattern row

def rowsReady (pattern : Atom) (rows : List Atom) : Bool := rows.all (rowReady pattern)

theorem relevant_rows_are_ground (pattern : Atom) (rows : List Atom)
    (ready : rowsReady pattern rows = true) (row : Atom) (member : row ∈ rows)
    (notScreened : rigidHeadClash pattern row = false) : isGroundAtom row = true := by
  have checked := List.all_eq_true.mp ready row member
  simpa [rowReady, notScreened] using checked

theorem ground_rows_are_ready (pattern : Atom) (rows : List Atom)
    (ground : ∀ row ∈ rows, isGroundAtom row = true) : rowsReady pattern rows = true := by
  apply List.all_eq_true.mpr
  intro row member
  simp [rowReady, ground row member]

def capturesReady (caller : Subst) (pattern : Atom) : Bool :=
  (atomFreeVars pattern).all fun name => match Subst.lookup caller name with
    | none => true
    | some value => isGroundAtom value

theorem capturesReady_closed (caller : Subst) (pattern : Atom)
    (ready : capturesReady caller pattern = true) (name : String) (used : name ∈ atomFreeVars pattern)
    (value : Atom) (found : Subst.lookup caller name = some value) : isGroundAtom value = true := by
  have checked := List.all_eq_true.mp ready name used
  simpa only [found] using checked

/-- An empty payload stream makes no destination query. Otherwise the full
current destination is checked against every prospective insertion. -/
def targetReady (before : Effects.State) (target : Handle) (payloads : List Atom) : Bool :=
  if payloads = [] then true else
    match before.read target with
    | none => false
    | some rows => payloads.all (fun payload => rowsReady payload rows)

def phaseReady (caller : Subst) (pattern : Atom) (rows : List Atom)
    (before : Effects.State) (target : Handle) (payloads : List Atom) : Bool :=
  capturesReady caller pattern && rowsReady pattern rows && targetReady before target payloads

theorem target_empty_has_no_read_dependency (before : Effects.State) (target : Handle) :
    targetReady before target [] = true := rfl

theorem missing_nonempty_target_refuses (before : Effects.State) (target : Handle) (payload : Atom) (rest : List Atom)
    (missing : before.read target = none) : targetReady before target (payload :: rest) = false := by
  simp [targetReady, missing]

namespace Controls

def edgePattern : Atom := .expression [.symbol "edge", .grounded (.int 0), .var "y"]
def openEdge : Atom := .expression [.symbol "edge", .var "x", .grounded (.int 1)]
def unrelatedEquation : Atom := .expression [.symbol "=", .expression [.symbol "f", .var "x"], .var "x"]

theorem open_candidate_is_not_an_absence_certificate : rowReady edgePattern openEdge = false := by decide +kernel

theorem unrelated_open_equation_can_be_screened : rowReady edgePattern unrelatedEquation = true := by decide +kernel

theorem unknown_head_is_not_a_clash :
    rowReady edgePattern (.expression [.var "head", .grounded (.int 0)]) = false := by decide +kernel

theorem cons_view_is_not_a_rigid_head_filter :
    rowReady (.expression [.symbol "cons", .var "head", .var "tail"]) openEdge = false := by decide +kernel

theorem open_capture_requires_the_unifying_route :
    capturesReady [("x", .expression [.symbol "f", .var "y"])] (.expression [.symbol "edge", .var "x"]) = false := by
  decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedQueryAdmission
