import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceInput

/-!
# Visible registry extensions for numbered source certificates

The check preserves successful first-match lookups. New keys and invisible
duplicate entries remain unrestricted. It transports existing syntax/cache
certificates in the same input; it grants no declaration or theorem authority
and compares no independently chosen source-history interpretations.
This whole-visible-table licence is stronger than the support of one cache;
a rebinding outside that support need not invalidate that cache.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceRegistry

open Lean Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open NumberedSourceSyntax NumberedSourceInput

universe u

private def lookupCheck {A : Type u} (same : A → A → Bool)
    (before after : List (String × A)) : Bool :=
  (before.map Prod.fst).all fun key => match List.lookup key before, List.lookup key after with
    | none, _ => true
    | some old, some new => same old new
    | some _, none => false

private theorem lookup_key_mem {A : Type u} (key : String) (values : List (String × A)) (value : A)
    (found : List.lookup key values = some value) : key ∈ values.map Prod.fst := by
  induction values with
  | nil => simp [List.lookup] at found
  | cons entry rest ih =>
      rcases entry with ⟨name, stored⟩
      cases matched : (key == name) with
      | true => exact List.mem_cons.mpr (.inl (eq_of_beq matched))
      | false =>
          have later : List.lookup key rest = some value := by
            simpa only [List.lookup, matched] using found
          exact List.mem_cons_of_mem _ (ih later)

private theorem lookupCheck_eq_true_iff {A : Type u} (same : A → A → Bool)
    (exactSame : ∀ first second, same first second = true ↔ first = second)
    (before after : List (String × A)) :
    lookupCheck same before after = true ↔
      ∀ key value, List.lookup key before = some value → List.lookup key after = some value := by
  constructor
  · intro checked key value found
    have accepted := List.all_eq_true.mp checked key (lookup_key_mem key before value found)
    rw [found] at accepted
    cases following : List.lookup key after with
    | none => simp [following] at accepted
    | some other =>
        have equal := (exactSame value other).mp (by simpa only [following] using accepted)
        exact congrArg some equal.symm
  · intro retained
    apply List.all_eq_true.mpr
    intro key _
    cases found : List.lookup key before with
    | none => rfl
    | some value =>
        rw [retained key value found]
        exact (exactSame value value).mpr rfl

structure LookupPreserving (before after : ExportCodec.Symbols) : Prop where
  operators : ∀ name operator, List.lookup name before.operators = some operator →
    List.lookup name after.operators = some operator
  constants : ∀ name constant, List.lookup name before.constants = some constant →
    List.lookup name after.constants = some constant

/-- Compare visible values, never an invisible duplicate pair's payload. -/
def preserves? (before after : ExportCodec.Symbols) : Bool :=
  lookupCheck TypeOp.same before.operators after.operators &&
    lookupCheck Const.same before.constants after.constants

theorem preserves?_eq_true_iff (before after : ExportCodec.Symbols) :
    preserves? before after = true ↔ LookupPreserving before after := by
  constructor
  · intro checked
    have checks : lookupCheck TypeOp.same before.operators after.operators = true ∧
        lookupCheck Const.same before.constants after.constants = true := by
      cases operators : lookupCheck TypeOp.same before.operators after.operators <;>
        cases constants : lookupCheck Const.same before.constants after.constants <;> simp_all [preserves?]
    obtain ⟨operators, constants⟩ := checks
    exact ⟨(lookupCheck_eq_true_iff TypeOp.same TypeOp.same_eq_true_iff _ _).mp operators,
      (lookupCheck_eq_true_iff Const.same Const.same_eq_true_iff _ _).mp constants⟩
  · intro retained
    have operators := (lookupCheck_eq_true_iff TypeOp.same TypeOp.same_eq_true_iff _ _).mpr retained.operators
    have constants := (lookupCheck_eq_true_iff Const.same Const.same_eq_true_iff _ _).mpr retained.constants
    change (_ && _) = true
    rw [operators, constants]
    rfl

theorem LookupPreserving.refl (symbols : ExportCodec.Symbols) : LookupPreserving symbols symbols :=
  ⟨fun _ _ found => found, fun _ _ found => found⟩

theorem LookupPreserving.trans {first middle last : ExportCodec.Symbols}
    (before : LookupPreserving first middle) (after : LookupPreserving middle last) :
    LookupPreserving first last :=
  ⟨fun name operator found => after.operators name operator (before.operators name operator found),
    fun name constant found => after.constants name constant (before.constants name constant found)⟩

private theorem children_transport_step {before after : ExportCodec.Symbols} (rows : Nat → Option Json)
    (limit : Nat)
    (children : ∀ child, child < limit → ∀ type, TypeAt before rows child type → TypeAt after rows child type)
    {indices : List Nat} {arguments : List Ty} (read : TypeChildrenAt before rows limit indices arguments) :
    TypeChildrenAt after rows limit indices arguments := by
  induction indices generalizing arguments with
  | nil => cases read; exact .nil
  | cons child rest ih =>
      cases read with
      | cons earlier typed later => exact .cons earlier (children _ earlier _ typed) (ih later)

theorem typeAt_transport {before after : ExportCodec.Symbols} (retained : LookupPreserving before after)
    (rows : Nat → Option Json) (index : Nat) (type : Ty) (read : TypeAt before rows index type) :
    TypeAt after rows index type := by
  induction index using Nat.strong_induction_on generalizing type with
  | h index ih =>
      cases read with
      | «variable» atRow parsed => exact .variable atRow parsed
      | operation atRow parsed registered children =>
          exact .operation atRow parsed (retained.operators _ _ registered)
            (children_transport_step rows index ih children)

theorem typeChildrenAt_transport {before after : ExportCodec.Symbols} (retained : LookupPreserving before after)
    (rows : Nat → Option Json) (limit : Nat) (indices : List Nat) (arguments : List Ty)
    (read : TypeChildrenAt before rows limit indices arguments) : TypeChildrenAt after rows limit indices arguments :=
  children_transport_step rows limit (fun child _ type typed => typeAt_transport retained rows child type typed) read

theorem termAt_transport {before after : ExportCodec.Symbols} (retained : LookupPreserving before after)
    (types terms : Nat → Option Json) (index : Nat) (term : SourceTerm) (read : TermAt before types terms index term) :
    TermAt after types terms index term := by
  induction read with
  | «variable» atRow parsed typed => exact .variable atRow parsed (typeAt_transport retained _ _ _ typed)
  | constant atRow parsed registered typed =>
      exact .constant atRow parsed (retained.constants _ _ registered) (typeAt_transport retained _ _ _ typed)
  | application atRow parsed earlierLeft earlierRight left right ihLeft ihRight =>
      exact .application atRow parsed earlierLeft earlierRight ihLeft ihRight
  | abstraction atRow parsed earlierBinder earlierBody binder body ihBinder ihBody =>
      exact .abstraction atRow parsed earlierBinder earlierBody ihBinder ihBody

theorem typeCache_transport {before after : ExportCodec.Symbols} (retained : LookupPreserving before after)
    (rows : Nat → Option Json) (cache : Nat → Option Ty) (correct : TypeCacheCorrect before rows cache) :
    TypeCacheCorrect after rows cache :=
  fun index type found => typeAt_transport retained rows index type (correct index type found)

theorem termCache_transport {before after : ExportCodec.Symbols} (retained : LookupPreserving before after)
    (types terms : Nat → Option Json) (cache : Nat → Option SourceTerm)
    (correct : TermCacheCorrect before types terms cache) : TermCacheCorrect after types terms cache :=
  fun index term found => termAt_transport retained types terms index term (correct index term found)

/-- Consume the existing numbered-envelope theorem after the checked registry
transport, retaining the actual row, identifier, body and cached source term. -/
theorem certified_term_readback {before after : ExportCodec.Symbols} (checked : preserves? before after = true)
    (types : Nat → Option Json) (raw bodies : List Json) (numbered : NumberedAt 0 raw bodies)
    (cache : Nat → Option SourceTerm) (correct : TermCacheCorrect before types (fun index => bodies[index]?) cache)
    (index : Nat) (term : SourceTerm) (found : cache index = some term) :
    ∃ original body, raw[index]? = some original ∧ identifier? original = some index ∧
      ExportCodec.at? original 1 = some body ∧ bodies[index]? = some body ∧
      TermAt after types (fun index => bodies[index]?) index term :=
  NumberedSourceInput.certified_term_readback after types raw bodies numbered cache
    (termCache_transport ((preserves?_eq_true_iff before after).mp checked) _ _ _ correct) index term found

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceRegistry
