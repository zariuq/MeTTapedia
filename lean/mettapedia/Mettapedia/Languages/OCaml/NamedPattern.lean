import Mettapedia.Languages.OCaml.PatternMatching

/-! Named source patterns bind name/value pairs in source order. Their
declarative matching judgment does not call the runtime pattern matcher.
Erasure supplies the existing indexed machine's anonymous slots. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

inductive NamedPattern where
  | variable (name : String)
  | wildcard
  | literal (value : Literal)
  | tuple (fields : List NamedPattern)
  | cons (head tail : NamedPattern)
  | variant (typeId constructor : Nat) (fields : List NamedPattern)
  deriving Repr, BEq

namespace NamedPattern

def erase : NamedPattern → MatchPattern
  | .variable _ => .bind
  | .wildcard => .wildcard
  | .literal value => .literal value
  | .tuple fields => .tuple (fields.map erase)
  | .cons head tail => .cons (erase head) (erase tail)
  | .variant typeId constructor fields => .variant typeId constructor (fields.map erase)

def names : NamedPattern → List String
  | .variable name => [name]
  | .wildcard | .literal _ => []
  | .tuple fields | .variant _ _ fields => fields.flatMap names
  | .cons head tail => names head ++ names tail

abbrev Bindings := List (String × Value)

mutual
  inductive Matches : NamedPattern → Value → Bindings → Prop where
    | variable (name : String) (value : Value) : Matches (.variable name) value [(name, value)]
    | wildcard (value : Value) : Matches .wildcard value []
    | literal (value : Literal) : Matches (.literal value) (.literal value) []
    | tuple {patterns values bindings} (fields : FieldsMatch patterns values bindings) :
        Matches (.tuple patterns) (.tuple values) bindings
    | cons {head tail first rest firstBindings restBindings}
        (headMatch : Matches head first firstBindings) (tailMatch : Matches tail rest restBindings) :
        Matches (.cons head tail) (.cons first rest) (firstBindings ++ restBindings)
    | variant {typeId constructor patterns values bindings} (fields : FieldsMatch patterns values bindings) :
        Matches (.variant typeId constructor patterns) (.variant typeId constructor values) bindings

  inductive FieldsMatch : List NamedPattern → List Value → Bindings → Prop where
    | nil : FieldsMatch [] [] []
    | cons {pattern patterns value values firstBindings restBindings}
        (first : Matches pattern value firstBindings) (rest : FieldsMatch patterns values restBindings) :
        FieldsMatch (pattern :: patterns) (value :: values) (firstBindings ++ restBindings)
end

mutual
  theorem matches_names {pattern : NamedPattern} {value : Value} {bindings : Bindings}
      (matched : Matches pattern value bindings) : bindings.map Prod.fst = pattern.names :=
    match matched with
    | .variable _ _ | .wildcard _ | .literal _ => by simp [names]
    | .tuple fields | .variant fields => by simpa only [names] using fields_names fields
    | .cons first rest => by simp only [List.map_append, matches_names first, matches_names rest, names]
    termination_by structural matched

  theorem fields_names {patterns : List NamedPattern} {values : List Value} {bindings : Bindings}
      (matched : FieldsMatch patterns values bindings) : bindings.map Prod.fst = patterns.flatMap names :=
    match matched with
    | .nil => rfl
    | .cons first rest => by simp only [List.map_append, matches_names first, fields_names rest, List.flatMap_cons]
    termination_by structural matched
end

mutual
  theorem matches_erased {pattern : NamedPattern} {value : Value} {bindings : Bindings}
      (matched : Matches pattern value bindings) : matchPattern pattern.erase value = some (bindings.map Prod.snd) :=
    match matched with
    | .variable _ _ | .wildcard _ => by simp [erase, matchPattern]
    | .literal value => by simp [erase, matchPattern]
    | .tuple fields | .variant fields => by simpa [erase, matchPattern] using fields_erased fields
    | .cons first rest => by simp [erase, matchPattern, matches_erased first, matches_erased rest, List.map_append]
    termination_by structural matched

  theorem fields_erased {patterns : List NamedPattern} {values : List Value} {bindings : Bindings}
      (matched : FieldsMatch patterns values bindings) :
      matchFields (patterns.map erase) values = some (bindings.map Prod.snd) :=
    match matched with
    | .nil => rfl
    | .cons first rest => by simp [matchFields, matches_erased first, fields_erased rest, List.map_append]
    termination_by structural matched
end

#print axioms matches_names
#print axioms fields_names
#print axioms matches_erased
#print axioms fields_erased

end NamedPattern
end Mettapedia.Languages.OCaml
