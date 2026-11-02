import Mettapedia.Languages.MeTTa.OSLFCore.State
import Mettapedia.Languages.MeTTa.SubstitutionAlgebra
import Mathlib.Logic.Relation

/-!
# Finite extensional register rules of Meta-MeTTa

This source profile follows the displayed register rules of Section 3.3 in
arXiv:2305.17218v1. It uses the existing finite expression atoms and four
registers. Comprehensions, streams, host arithmetic and the paper's compiler
are not identified with this fragment. HE evaluation remains independent.

Unification uses an explicitly declared principal-unifier interpretation of
the paper's unspecified operation, certified by solutions and factorization.
It does not inherit the older executable prototype's algorithm. A selected knowledge occurrence contributes
one receipt, retaining multiplicity and its chosen one-hole context. Query
and Chain gather their family into one workspace. Transform uses its explicit
template, not an equation RHS. Its remainder insensitivity is the paper's
equation-LHS condition; it is not silently strengthened to contextual coverage.

The displayed indexing does not settle whether empty matching families are
allowed. Both named policies are retained, with the same nonempty controls.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.OSLFCore.MetaMeTTa

open Mettapedia.Languages.MeTTa.SubstitutionAlgebra
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Insertion (single)

/-- A single selected expression position, including nested positions. -/
inductive Context where
  | hole
  | expression (before : List Atom) (inside : Context) (after : List Atom)

def Context.fill : Context → Atom → Atom
  | .hole, value => value
  | .expression before inside after, value => .expression (before ++ inside.fill value :: after)

def Context.comp : Context → Context → Context
  | .hole, inner => inner
  | .expression before inside after, inner => .expression before (inside.comp inner) after

theorem Context.fill_comp (outer inner : Context) (value : Atom) :
    (outer.comp inner).fill value = outer.fill (inner.fill value) := by
  induction outer with
  | hole => rfl
  | expression before inside after ih => simp only [Context.comp, Context.fill, ih]

def Context.substitute (replacement : Subst) : Context → Context
  | .hole => .hole
  | .expression before inside after =>
      .expression (subst.substList replacement before) (inside.substitute replacement)
        (subst.substList replacement after)

theorem Context.subst_fill (replacement : Subst) (context : Context) (value : Atom) :
    subst replacement (context.fill value) = (context.substitute replacement).fill (subst replacement value) := by
  induction context with
  | hole => rfl
  | expression before inside after ih =>
      simp only [Context.fill, Context.substitute, subst, substList_append, subst.substList, ih]

/-- Applying a substitution only to the selected replacement agrees with
applying it to the whole filled term when the surrounding context is fixed. -/
theorem Context.local_subst_eq_whole (replacement : Subst) (context : Context)
    (fixed : context.substitute replacement = context) (value : Atom) :
    context.fill (subst replacement value) = subst replacement (context.fill value) := by
  rw [Context.subst_fill, fixed]

structure Principal (left right : Atom) (answer : Subst) : Prop where
  solves : subst answer left = subst answer right
  factors : ∀ candidate : Subst, subst candidate left = subst candidate right →
    ∃ residual : Subst, ∀ value, subst candidate value = subst residual (subst answer value)

theorem principal_refl (value : Atom) : Principal value value empty :=
  ⟨rfl, fun candidate _ => ⟨candidate, fun term => by rw [subst_empty]⟩⟩

theorem principal_variable (name : String) (value : Atom) (fresh : name ∉ vars value) :
    Principal (.var name) value (single name value) := by
  have unchanged : subst (single name value) value = value := by
    apply subst_eq_self_of_silentOn
    intro other member
    have different : other ≠ name := fun same => fresh (same ▸ member)
    simp [single, different]
  refine ⟨?_, ?_⟩
  · rw [Insertion.subst_single_variable]
    exact unchanged.symm
  · intro candidate solves
    refine ⟨candidate, fun term => ?_⟩
    rw [subst_subst]
    apply (subst_eq_iff_on_vars candidate (comp (single name value) candidate) term).mpr
    intro other _
    by_cases same : other = name
    · subst other
      simpa [subst, comp, single] using solves
    · simp [subst, comp, single, same]

/-- Ground selected values and template support make the observable result
independent of which principal unifier certificate is chosen. Without those
conditions, a solver/renaming observation contract is still needed. -/
theorem grounded_template_result_is_determined (context : Context) (query template value : Atom)
    (ground : vars value = []) (covered : ∀ name ∈ vars template, name ∈ vars query)
    {first second : Subst} (one : Principal query value first) (two : Principal query value second) :
    context.fill (subst first template) = context.fill (subst second template) := by
  apply congrArg context.fill
  apply subst_template_eq_of_pattern_eq first second query template covered
  exact one.solves.trans ((subst_of_vars_eq_nil first value ground).trans
    ((subst_of_vars_eq_nil second value ground).symm.trans two.solves.symm))

def Insensitive (query : Atom) (knowledge : Multiset Atom) : Prop :=
  ∀ left right, Atom.equality left right ∈ knowledge →
    ¬ ∃ candidate : Subst, subst candidate query = subst candidate left

theorem insensitive_empty (query : Atom) : Insensitive query 0 :=
  fun _ _ member => False.elim (Multiset.notMem_zero _ member)

/-- A stronger, explicitly separate remainder condition for contextual
matching. The displayed paper condition above only inspects equation LHSs. -/
def ContextInsensitive (query : Atom) (knowledge : Multiset Atom) : Prop :=
  ∀ context : Context, ∀ value, context.fill value ∈ knowledge →
    ¬ ∃ candidate : Subst, subst candidate query = subst candidate value

theorem ContextInsensitive.insensitive {query : Atom} {knowledge : Multiset Atom}
    (complete : ContextInsensitive query knowledge) : Insensitive query knowledge := by
  intro left right member
  exact complete (.expression [.symbol "="] .hole [right]) left member

inductive EmptyFamily where
  | allowed
  | forbidden
  deriving DecidableEq

def EmptyFamily.Admits : EmptyFamily → Nat → Prop
  | .allowed, _ => True
  | .forbidden, count => 0 < count

structure EquationUse (query : Atom) where
  left : Atom
  right : Atom
  answer : Subst
  principal : Principal query left answer

def EquationUse.entry {query : Atom} (use : EquationUse query) : Atom :=
  Atom.equality use.left use.right

def EquationUse.result {query : Atom} (context : Context) (use : EquationUse query) : Atom :=
  context.fill (subst use.answer use.right)

structure ContextUse (query : Atom) where
  context : Context
  value : Atom
  answer : Subst
  principal : Principal query value answer

def ContextUse.entry {query : Atom} (use : ContextUse query) : Atom := use.context.fill use.value
def ContextUse.result {query : Atom} (template : Atom) (use : ContextUse query) : Atom :=
  use.context.fill (subst use.answer template)

def transform (query template : Atom) : Atom := .expression [.symbol "transform", query, template]
def addAtom (value : Atom) : Atom := .expression [.symbol "addAtom", value]
def remAtom (value : Atom) : Atom := .expression [.symbol "remAtom", value]
def unit : Atom := .expression []

/-- The eight displayed register rules, with an explicit empty-family
interpretation. Premises contain no reference to Prime or its candidate. -/
inductive Step (policy : EmptyFamily) : MeTTaState → MeTTaState → Prop where
  | query (input rest workspace output : Multiset Atom) (context : Context) (query : Atom)
      (uses : List (EquationUse query))
      (size : policy.Admits uses.length) (closed : Insensitive query rest) :
      Step policy
        ⟨context.fill query ::ₘ input, ⟨(uses.map EquationUse.entry : Multiset Atom) + rest⟩, workspace, output⟩
        ⟨input, ⟨(uses.map EquationUse.entry : Multiset Atom) + rest⟩,
          (uses.map (EquationUse.result context) : Multiset Atom) + workspace, output⟩
  | chain (input rest workspace output : Multiset Atom) (context : Context) (query : Atom)
      (uses : List (EquationUse query))
      (size : policy.Admits uses.length) (closed : Insensitive query rest) :
      Step policy
        ⟨input, ⟨(uses.map EquationUse.entry : Multiset Atom) + rest⟩, context.fill query ::ₘ workspace, output⟩
        ⟨input, ⟨(uses.map EquationUse.entry : Multiset Atom) + rest⟩,
          (uses.map (EquationUse.result context) : Multiset Atom) + workspace, output⟩
  | transform (input rest workspace output : Multiset Atom) (query template : Atom)
      (uses : List (ContextUse query))
      (size : policy.Admits uses.length) (closed : Insensitive query rest) :
      Step policy
        ⟨MetaMeTTa.transform query template ::ₘ input,
          ⟨(uses.map ContextUse.entry : Multiset Atom) + rest⟩, workspace, output⟩
        ⟨input, ⟨(uses.map ContextUse.entry : Multiset Atom) + rest⟩,
          (uses.map (ContextUse.result template) : Multiset Atom) + workspace, output⟩
  | addInput (input knowledge workspace output : Multiset Atom) (value : Atom) :
      Step policy ⟨addAtom value ::ₘ input, ⟨knowledge⟩, workspace, output⟩
        ⟨input, ⟨knowledge + {value}⟩, workspace, unit ::ₘ output⟩
  | addKnowledge {before after : MeTTaState} (value : Atom) (base : Step policy before after) :
      Step policy { before with knowledge := ⟨addAtom value ::ₘ before.knowledge.atoms⟩ }
        { after with
          knowledge := ⟨addAtom value ::ₘ value ::ₘ after.knowledge.atoms⟩
          output := unit ::ₘ after.output }
  | removeInput (input knowledge workspace output : Multiset Atom) (value : Atom) :
      Step policy ⟨remAtom value ::ₘ input, ⟨value ::ₘ knowledge⟩, workspace, output⟩
        ⟨input, ⟨knowledge⟩, workspace, unit ::ₘ output⟩
  | removeKnowledge {before after : MeTTaState} (value : Atom) (base : Step policy before after) :
      Step policy { before with knowledge := ⟨remAtom value ::ₘ value ::ₘ before.knowledge.atoms⟩ }
        { after with
          knowledge := ⟨remAtom value ::ₘ after.knowledge.atoms⟩
          output := unit ::ₘ after.output }
  | output (input knowledge workspace output : Multiset Atom) (value : Atom)
      (closed : Insensitive value knowledge) :
      Step policy ⟨input, ⟨knowledge⟩, value ::ₘ workspace, output⟩
        ⟨input, ⟨knowledge⟩, workspace, value ::ₘ output⟩

def Reaches (policy : EmptyFamily) := Relation.ReflTransGen (Step policy)

end Mettapedia.Languages.MeTTa.OSLFCore.MetaMeTTa
