import Mettapedia.GSLT.Contracts.ACUReplacement

/-!
# Reuse of ground bag replacement for a declaration without a unit

An AC declaration has no unit rule. On unit-free inputs this module
reflects ACU equations into AC equations, and reflects ACU contextual
steps into contexts of the unit-free grammar. Thus the same multiset
reducer serves AC rules without silently licensing a unit operation.
An empty frame corresponds to an ordinary root contraction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.ACUReplacement.AC

universe u
variable {Atom : Type u}

inductive UnitFree : Term Atom → Prop where
  | atom (a : Atom) : UnitFree (.atom a)
  | op {a b : Term Atom} : UnitFree a → UnitFree b → UnitFree (.op a b)

theorem UnitFree.operands_pos {p : Term Atom} (free : UnitFree p) : 0 < (operands p).card := by
  induction free with
  | atom _ => simp [operands]
  | op _ _ first _ =>
      simp only [operands, Multiset.card_add]
      omega

private theorem spell_cons (a : Atom) (rest : List Atom) :
    ∃ p : Term Atom, UnitFree p ∧ operands p = (a :: rest : List Atom) := by
  induction rest generalizing a with
  | nil => exact ⟨.atom a, .atom a, rfl⟩
  | cons b rest ih =>
      obtain ⟨tail, free, same⟩ := ih b
      exact ⟨.op (.atom a) tail, .op (.atom a) free,
        by simp [operands, same, Multiset.singleton_add]⟩

theorem exists_unitFree_spelling (bag : Multiset Atom) (nonempty : bag ≠ 0) :
    ∃ p : Term Atom, UnitFree p ∧ operands p = bag := by
  obtain ⟨xs, same⟩ := Quotient.exists_rep bag
  cases xs with
  | nil => exact (nonempty same.symm).elim
  | cons a rest =>
      obtain ⟨p, free, agrees⟩ := spell_cons a rest
      exact ⟨p, free, agrees.trans same⟩

inductive Equation : Term Atom → Term Atom → Prop where
  | refl (a : Term Atom) : Equation a a
  | symm {a b : Term Atom} : Equation a b → Equation b a
  | trans {a b c : Term Atom} : Equation a b → Equation b c → Equation a c
  | swap (a b : Term Atom) : Equation (.op a b) (.op b a)
  | assoc (a b c : Term Atom) : Equation (.op (.op a b) c) (.op a (.op b c))
  | op {a a' b b' : Term Atom} : Equation a a' → Equation b b' → Equation (.op a b) (.op a' b')

theorem Equation.toACU {a b : Term Atom} (eq : Equation a b) : ACUReplacement.Equation a b := by
  induction eq with
  | refl a => exact .refl a
  | symm _ ih => exact .symm ih
  | trans _ _ first second => exact .trans first second
  | swap a b => exact .swap a b
  | assoc a b c => exact .assoc a b c
  | op _ _ first second => exact .op first second

private def fuse (a b : Option (Term Atom)) : Option (Term Atom) :=
  match a, b with
  | none, opt | opt, none => opt
  | some a, some b => some (.op a b)

private def removeUnits : Term Atom → Option (Term Atom)
  | .atom a => some (.atom a)
  | .unit => none
  | .op a b => fuse (removeUnits a) (removeUnits b)

private theorem remove_of_unitFree {a : Term Atom} (valid : UnitFree a) :
    removeUnits a = some a := by
  induction valid with
  | atom _ => rfl
  | op _ _ first second => simp [removeUnits, first, second, fuse]

private theorem unitFree_of_remove {a clean : Term Atom} (found : removeUnits a = some clean) :
    UnitFree clean := by
  induction a generalizing clean with
  | atom name =>
      cases found
      exact .atom name
  | unit => cases found
  | op a b ihA ihB =>
      cases first : removeUnits a with
      | none =>
          rw [removeUnits, first] at found
          exact ihB found
      | some left =>
          cases second : removeUnits b with
          | none =>
              rw [removeUnits, first, second] at found
              exact Option.some.inj found ▸ ihA first
          | some right =>
              rw [removeUnits, first, second] at found
              cases found
              exact .op (ihA first) (ihB second)

private theorem fuse_respects {a c b d : Option (Term Atom)}
    (first : Option.Rel Equation a b) (second : Option.Rel Equation c d) :
    Option.Rel Equation (fuse a c) (fuse b d) := by
  cases first <;> cases second
  · exact .some (.op ‹Equation _ _› ‹Equation _ _›)
  · exact .some ‹Equation _ _›
  · exact .some ‹Equation _ _›
  · exact .none

private theorem reflOption (a : Option (Term Atom)) : Option.Rel Equation a a := by
  cases a with
  | none => exact .none
  | some a => exact .some (.refl a)

private theorem symmOption {a b : Option (Term Atom)} (eq : Option.Rel Equation a b) :
    Option.Rel Equation b a := by
  cases eq with
  | none => exact .none
  | some eq => exact .some (.symm eq)

private theorem transOption {a b c : Option (Term Atom)}
    (first : Option.Rel Equation a b) (second : Option.Rel Equation b c) :
    Option.Rel Equation a c := by
  cases first with
  | none => cases second; exact .none
  | some first => cases second with | some second => exact .some (.trans first second)

private theorem remove_respects {a b : Term Atom} (eq : ACUReplacement.Equation a b) :
    Option.Rel Equation (removeUnits a) (removeUnits b) := by
  induction eq with
  | refl a => exact reflOption (removeUnits a)
  | symm _ ih => exact symmOption ih
  | trans _ _ first second => exact transOption first second
  | rightUnit a =>
      change Option.Rel Equation (fuse (removeUnits a) none) (removeUnits a)
      cases removeUnits a <;> exact reflOption _
  | swap a b =>
      change Option.Rel Equation (fuse (removeUnits a) (removeUnits b))
        (fuse (removeUnits b) (removeUnits a))
      cases removeUnits a <;> cases removeUnits b
      · exact .none
      · exact reflOption _
      · exact reflOption _
      · exact .some (.swap _ _)
  | assoc a b c =>
      change Option.Rel Equation (fuse (fuse (removeUnits a) (removeUnits b)) (removeUnits c))
        (fuse (removeUnits a) (fuse (removeUnits b) (removeUnits c)))
      cases removeUnits a <;> cases removeUnits b <;> cases removeUnits c
      any_goals exact reflOption _
      exact .some (.assoc _ _ _)
  | op _ _ first second => exact fuse_respects first second

theorem equation_iff_operands {a b : Term Atom} (aFree : UnitFree a) (bFree : UnitFree b) :
    Equation a b ↔ operands a = operands b := by
  refine ⟨fun eq => eq.toACU.sameOperands, fun same => ?_⟩
  have reflected := remove_respects (ACUReplacement.equation_iff_operands.mpr same)
  rw [remove_of_unitFree aFree, remove_of_unitFree bFree] at reflected
  cases reflected with
  | some eq => exact eq

inductive UnitFreeContext : Context Atom → Prop where
  | hole : UnitFreeContext .hole
  | left {c : Context Atom} {kept : Term Atom} :
      UnitFreeContext c → UnitFree kept → UnitFreeContext (.left c kept)
  | right {c : Context Atom} {kept : Term Atom} :
      UnitFree kept → UnitFreeContext c → UnitFreeContext (.right kept c)

private def cleanContext : Context Atom → Context Atom
  | .hole => .hole
  | .left c kept =>
      match removeUnits kept with
      | none => cleanContext c
      | some term => .left (cleanContext c) term
  | .right kept c =>
      match removeUnits kept with
      | none => cleanContext c
      | some term => .right term (cleanContext c)

private theorem cleanContext_free (context : Context Atom) : UnitFreeContext (cleanContext context) := by
  induction context with
  | hole => exact .hole
  | left _ kept ih =>
      cases normal : removeUnits kept <;> simp only [cleanContext, normal]
      · exact ih
      · exact .left ih (unitFree_of_remove normal)
  | right kept _ ih =>
      cases normal : removeUnits kept <;> simp only [cleanContext, normal]
      · exact ih
      · exact .right (unitFree_of_remove normal) ih

private theorem remove_plug (context : Context Atom) {a : Term Atom} (aFree : UnitFree a) :
    removeUnits (context.plug a) = some ((cleanContext context).plug a) := by
  induction context with
  | hole => exact remove_of_unitFree aFree
  | left _ kept ih | right kept _ ih =>
      cases normal : removeUnits kept <;>
        simp only [Context.plug, removeUnits, ih, normal, fuse, cleanContext]

theorem mem_successors_iff_ac_context [DecidableEq Atom] (rules : List (Rule Atom))
    (rulesFree : ∀ r ∈ rules, UnitFree r.lhs ∧ UnitFree r.rhs)
    {a b : Term Atom} (aFree : UnitFree a) (bFree : UnitFree b) :
    operands b ∈ successors rules (operands a) ↔
      ∃ rule ∈ rules, ∃ context : Context Atom, UnitFreeContext context ∧
        Equation a (context.plug rule.lhs) ∧ Equation (context.plug rule.rhs) b := by
  rw [mem_successors_iff, reduces_iff_context]
  constructor
  · rintro ⟨rule, declared, context, before, after⟩
    have first := remove_respects before
    have second := remove_respects after
    obtain ⟨lhsFree, rhsFree⟩ := rulesFree rule declared
    rw [remove_of_unitFree aFree, remove_plug _ lhsFree] at first
    rw [remove_plug _ rhsFree, remove_of_unitFree bFree] at second
    cases first with
    | some first =>
        cases second with
        | some second => exact ⟨rule, declared, cleanContext context, cleanContext_free _, first, second⟩
  · rintro ⟨rule, declared, context, _, before, after⟩
    exact ⟨rule, declared, context, before.toACU, after.toACU⟩

namespace Controls

theorem no_unit_law_in_ac :
    ¬ Equation (.op (.atom (0 : Nat)) .unit) (.atom 0) := by
  intro eq
  -- Interpret the undeclared unit as an ordinary leaf.
  have leaves {a b : Term Nat} (same : Equation a b) :
      sizeOf a = sizeOf b := by
    induction same with
    | refl _ => rfl
    | symm _ ih => exact ih.symm
    | trans _ _ first second => exact first.trans second
    | swap _ _ | assoc _ _ _ => simp [Term.op.sizeOf_spec]; omega
    | op _ _ first second => simp [Term.op.sizeOf_spec, first, second]
  have wrong := leaves eq
  simp [Term.op.sizeOf_spec, Term.atom.sizeOf_spec, Term.unit.sizeOf_spec] at wrong

private def replacePair : Rule Nat := ⟨.op (.atom 0) (.atom 1), .atom 2⟩

theorem root_replacement_has_no_unit_context :
    operands (.atom 2) ∈ successors [replacePair] (operands replacePair.lhs) ∧
      UnitFreeContext (.hole : Context Nat) := by
  exact ⟨by decide, .hole⟩

end Controls

#print axioms equation_iff_operands
#print axioms mem_successors_iff_ac_context
#print axioms Controls.no_unit_law_in_ac
#print axioms Controls.root_replacement_has_no_unit_context

end Mettapedia.GSLT.Contracts.ACUReplacement.AC
