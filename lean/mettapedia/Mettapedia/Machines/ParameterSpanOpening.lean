import Mettapedia.OSLF.MeTTaIL.Substitution
import Mathlib.Tactic

/-!
# Opening a parameter span in one traversal

The source repeatedly eliminates the outermost remaining binder, using the
maintained MeTTaIL substitution. The target traverses the body once, reading
free parameter variables by their bound-index position. Parameters arrive in
outer-to-inner order; the index lookup therefore uses their reverse.

The theorem covers arbitrary nested lambda and multi-lambda scopes, explicit
substitutions, ordered arguments and collections. Parameters are free variables,
not arbitrary argument syntax. Execution binds them to already ready values.
Native array bounds, overflow, pointer sharing, allocation failure and the C
declaration-to-scope correspondence retain their native controls.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ParameterSpanOpening

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

/-- The vector is in bound-index order: the innermost parameter is first. -/
def atDepth (depth : Nat) (parameters : List String) : Pattern → Pattern
  | .bvar index =>
      if index < depth then .bvar index
      else match parameters[index - depth]? with
        | some name => .fvar name
        | none => .bvar (index - parameters.length)
  | .fvar name => .fvar name
  | .apply constructor args => .apply constructor (args.map (atDepth depth parameters))
  | .lambda name body => .lambda name (atDepth (depth + 1) parameters body)
  | .multiLambda arity names body =>
      .multiLambda arity names (atDepth (depth + arity) parameters body)
  | .subst body replacement =>
      .subst (atDepth (depth + 1) parameters body) (atDepth depth parameters replacement)
  | .collection kind elements rest =>
      .collection kind (elements.map (atDepth depth parameters)) rest
termination_by body => sizeOf body
decreasing_by all_goals sizeOf_pattern_dec

/-- Eliminate outer parameters first, as successive unary callable opening does. -/
def reference (depth : Nat) : List String → Pattern → Pattern
  | [], body => body
  | name :: rest, body =>
      reference depth rest (instantiateBVarAt (depth + rest.length) (.fvar name) body)

private theorem index_append_outer (depth index : Nat) (parameters : List String)
    (outer : String) :
    atDepth depth parameters
      (instantiateBVarAt (depth + parameters.length) (.fvar outer) (.bvar index)) =
    atDepth depth (parameters ++ [outer]) (.bvar index) := by
  by_cases inner : index < depth
  · have before : index < depth + parameters.length := by omega
    simp [instantiateBVarAt, atDepth, inner, before]
  · by_cases before : index < depth + parameters.length
    · have offset : index - depth < parameters.length := by omega
      cases found : parameters[index - depth]? with
      | none =>
          have := List.getElem?_eq_none_iff.mp found
          omega
      | some name =>
          simp [instantiateBVarAt, atDepth, inner, before, List.getElem?_append,
            offset]
    · by_cases selected : index = depth + parameters.length
      · subst index
        simp [instantiateBVarAt, atDepth, liftBVars]
      · have outside : parameters.length ≤ index - 1 - depth := by omega
        have outside' : (parameters ++ [outer]).length ≤ index - depth := by
          simp only [List.length_append, List.length_singleton]
          omega
        have found : parameters[index - 1 - depth]? = none :=
          List.getElem?_eq_none_iff.mpr outside
        have found' : (parameters ++ [outer])[index - depth]? = none :=
          List.getElem?_eq_none_iff.mpr outside'
        have remains : ¬index - 1 < depth := by omega
        simp [instantiateBVarAt, atDepth, inner, before, selected, found, found', remains]
        omega

theorem append_outer (body : Pattern) (depth : Nat) (parameters : List String)
    (outer : String) :
    atDepth depth parameters
      (instantiateBVarAt (depth + parameters.length) (.fvar outer) body) =
    atDepth depth (parameters ++ [outer]) body := by
  induction body using Pattern.inductionOn generalizing depth with
  | hbvar index => exact index_append_outer depth index parameters outer
  | hfvar name => simp [instantiateBVarAt, atDepth]
  | happly constructor args ih =>
      simp only [instantiateBVarAt, atDepth, List.map_map]
      congr 1
      exact List.map_congr_left fun child member => ih child member depth
  | hlambda name body ih =>
      simpa only [instantiateBVarAt, atDepth, Nat.add_right_comm] using
        congrArg (Pattern.lambda name) (ih (depth + 1))
  | hmultiLambda arity names body ih =>
      simpa only [instantiateBVarAt, atDepth, Nat.add_right_comm] using
        congrArg (Pattern.multiLambda arity names) (ih (depth + arity))
  | hsubst body replacement ihBody ihReplacement =>
      simp only [instantiateBVarAt, atDepth]
      congr 1
      · simpa only [Nat.add_right_comm] using ihBody (depth + 1)
      · exact ihReplacement depth
  | hcollection kind elements rest ih =>
      simp only [instantiateBVarAt, atDepth, List.map_map]
      congr 1
      exact List.map_congr_left fun child member => ih child member depth

theorem opening_refines (parameters : List String) (depth : Nat) (body : Pattern) :
    reference depth parameters body = atDepth depth parameters.reverse body := by
  induction parameters generalizing body with
  | nil =>
      induction body using Pattern.inductionOn generalizing depth with
      | hbvar index => simp [reference, atDepth]
      | hfvar name => simp [reference, atDepth]
      | happly constructor args ih =>
          simp only [reference, List.reverse_nil, atDepth]
          congr 1
          calc
            args = args.map id := (List.map_id' args).symm
            _ = args.map (atDepth depth []) := List.map_congr_left fun child member => by
              simpa only [reference, List.reverse_nil, id_eq] using ih child member depth
      | hlambda name body ih =>
          simpa only [reference, List.reverse_nil, atDepth] using
            congrArg (Pattern.lambda name) (ih (depth + 1))
      | hmultiLambda arity names body ih =>
          simpa only [reference, List.reverse_nil, atDepth] using
            congrArg (Pattern.multiLambda arity names) (ih (depth + arity))
      | hsubst body replacement ihBody ihReplacement =>
          simp only [reference, List.reverse_nil, atDepth]
          exact congrArg₂ Pattern.subst (ihBody (depth + 1)) (ihReplacement depth)
      | hcollection kind elements rest ih =>
          simp only [reference, List.reverse_nil, atDepth]
          congr 1
          calc
            elements = elements.map id := (List.map_id' elements).symm
            _ = elements.map (atDepth depth []) := List.map_congr_left fun child member => by
              simpa only [reference, List.reverse_nil, id_eq] using ih child member depth
  | cons name rest ih =>
      simp only [reference, ih, List.reverse_cons]
      simpa only [List.length_reverse] using append_outer body depth rest.reverse name

def openParameters (parameters : List String) (body : Pattern) : Pattern :=
  atDepth 0 parameters.reverse body

def wrap : Nat → Pattern → Pattern
  | 0, body => body
  | count + 1, body => .lambda none (wrap count body)

def peel : List String → Pattern → Option Pattern
  | [], body => some body
  | name :: rest, .lambda _ body => peel rest (instantiateBVarAt 0 (.fvar name) body)
  | _ :: _, _ => none

theorem instantiate_under_wrap (count depth : Nat) (name : String) (body : Pattern) :
    instantiateBVarAt depth (.fvar name) (wrap count body) =
      wrap count (instantiateBVarAt (depth + count) (.fvar name) body) := by
  induction count generalizing depth with
  | zero => simp [wrap]
  | succ count ih =>
      simpa only [wrap, instantiateBVarAt, Nat.add_right_comm, Nat.add_assoc] using
        congrArg (Pattern.lambda none) (ih (depth + 1))

theorem unary_opening_refines (parameters : List String) (body : Pattern) :
    peel parameters (wrap parameters.length body) = some (openParameters parameters body) := by
  have source : ∀ (parameters : List String) (body : Pattern),
      peel parameters (wrap parameters.length body) = some (reference 0 parameters body) := by
    intro parameters
    induction parameters with
    | nil => intro body; rfl
    | cons name rest ih =>
        intro body
        simp only [List.length_cons, wrap, peel, instantiate_under_wrap, Nat.zero_add]
        rw [ih]
        simp only [reference, Nat.zero_add]
  rw [source, opening_refines]
  rfl

theorem parameter_order :
    openParameters ["first", "second"]
      (.apply "Pair" [.bvar 1, .bvar 0]) =
      .apply "Pair" [.fvar "first", .fvar "second"] := by
  simp [openParameters, atDepth]

theorem inner_binder_is_protected :
    openParameters ["first", "second"] (.lambda none (.bvar 0)) =
      .lambda none (.bvar 0) := by
  simp [openParameters, atDepth]

theorem outer_indices_decrease :
    openParameters ["first", "second"] (.bvar 5) = .bvar 3 := by
  simp [openParameters, atDepth]

theorem reversing_parameters_changes_result :
    openParameters ["first", "second"] (.bvar 0) ≠
      openParameters ["second", "first"] (.bvar 0) := by
  decide +kernel

end Mettapedia.Machines.ParameterSpanOpening

#print axioms Mettapedia.Machines.ParameterSpanOpening.append_outer
#print axioms Mettapedia.Machines.ParameterSpanOpening.opening_refines
#print axioms Mettapedia.Machines.ParameterSpanOpening.instantiate_under_wrap
#print axioms Mettapedia.Machines.ParameterSpanOpening.unary_opening_refines
#print axioms Mettapedia.Machines.ParameterSpanOpening.parameter_order
#print axioms Mettapedia.Machines.ParameterSpanOpening.inner_binder_is_protected
#print axioms Mettapedia.Machines.ParameterSpanOpening.outer_indices_decrease
#print axioms Mettapedia.Machines.ParameterSpanOpening.reversing_parameters_changes_result
