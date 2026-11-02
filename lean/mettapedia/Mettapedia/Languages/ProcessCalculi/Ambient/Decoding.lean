import Mettapedia.Languages.ProcessCalculi.Ambient.FullEquivalences

/-!
# Reading located blocks back as ambient processes

A block of the located calculus is flat: restrictions over components, each component a marker `LAmb[p, ℓ, m]` (the
ambient `m` at location `ℓ` sits at `p`), a capability `LIn/LOut/LOpen[p, n, K]` at `p`, a prefix by a capability term
`LCap[p, M, K]`, an input `LInName/LInCap[p, (x).B]` or an output `LOutName/LOutCap[p, M]` at `p`, or a replication
`LRep[X]`, placed where the components of `X`'s block outside `X` are. A block is read back from a place
(`decodeForm`) as an ambient block over the same restrictions:

- every restriction stays a restriction, in its place: a restriction that served as a location is used by nothing in
  the reading, which the garbage law removes;
- the components placed at the place are read one by one (`readComponent`): a marker as its ambient, around the tree
  of the components placed at the ambient's location among those placed elsewhere, and an opened marker as that tree
  itself, in place; a capability as its capability, and a prefix by a capability term as that prefix, its
  continuation's block read at the place; an input as its input, its body's block read at the place under the
  binder; an output as its output; a replication as the replication of its argument's block read at the place.

Variables keep their indices. Fuel bounds the reading; a name position that holds no variable, a message position
that holds no message, and any other component, read as inaction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex decompose)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedBlock)

/-- Inaction, read back. -/
abbrev inaction : Pattern := .apply "AZero" []

/-- Whether a pattern is a variable. -/
def isVariable : Pattern → Bool
  | .bvar _ | .fvar _ => true
  | _ => false

/-- **Whether a pattern is a message**: a variable, `in n`, `out n` or `open n` over a variable, the empty path, or the
path of two messages. Names and capability terms are messages. -/
def isMessage : Pattern → Bool
  | .bvar _ | .fvar _ => true
  | .apply label [name] => decide (label ∈ ["CapIn", "CapOut", "CapOpen"]) && isVariable name
  | .apply label [] => label == "CapEps"
  | .apply label [first, second] => label == "CapPath" && isMessage first && isMessage second
  | _ => false

/-- A variable outside a block of `count` restrictions, as seen from outside. -/
def lowerBy (count : Nat) : Pattern → Option Pattern
  | .bvar index => if count ≤ index then some (.bvar (index - count)) else none
  | .fvar name => some (.fvar name)
  | _ => none

/-- The capabilities of the located calculus. -/
abbrev capabilities : List String := ["LIn", "LOut", "LOpen"]

/-- The markers of the located calculus: an ambient's, and an opened ambient's. -/
abbrev markers : List String := ["LAmb", "LOpened"]

/-- The inputs of the located calculus: of a name, and of a capability. -/
abbrev inputs : List String := ["LInName", "LInCap"]

/-- The outputs of the located calculus: of a name, and of a capability. -/
abbrev outputs : List String := ["LOutName", "LOutCap"]

/-- **A marker's content, read**: inside the ambient, or in place once the ambient is opened. -/
def wrapContent (label : String) (name content : Pattern) : Pattern :=
  if label = "LAmb" then .apply "AAmb" [name, content] else content

theorem wrapContent_amb (name content : Pattern) : wrapContent "LAmb" name content = .apply "AAmb" [name, content] := by
  simp [wrapContent]

theorem wrapContent_opened (name content : Pattern) : wrapContent "LOpened" name content = content := by
  simp [wrapContent]

/-- The ambient capability of a located one. -/
def ambientCapability (label : String) : String :=
  if label = "LIn" then "AIn" else if label = "LOut" then "AOut" else "AOpen"

/-- The ambient input of a located one. -/
def ambientInput (label : String) : String := if label = "LInName" then "AInName" else "AInCap"

/-- The ambient output of a located one. -/
def ambientOutput (label : String) : String := if label = "LOutName" then "AOutName" else "AOutCap"

mutual
  /-- **The place of a component**: a marker's parent, the place of a capability, of a prefix by a capability term, of
  an input or of an output, the outer place of a replication's argument. -/
  def placeOf : Nat → Pattern → Option Pattern
    | 0, _ => none
    | _ + 1, .apply label [place, _, _] =>
        if label ∈ markers ∨ label ∈ capabilities ∨ label = "LCap" then some place else none
    | _ + 1, .apply label [place, _] =>
        if label ∈ inputs ∨ label ∈ outputs then some place else none
    | fuel + 1, .apply label [argument] =>
        if label = "LRep" then outerPlace fuel (decompose locatedBlock argument) else none
    | _ + 1, _ => none

  /-- **The outer place of a block**: the place, outside the block, of its first component placed outside it. -/
  def outerPlace : Nat → Prenex → Option Pattern
    | 0, _ => none
    | fuel + 1, form => form.components.findSome? fun component =>
        (placeOf fuel component).bind (lowerBy form.count)
end

/-- **The place of a component**, read with fuel enough for the component: each replication around a component placed
inside it takes two steps. -/
def placeAt (component : Pattern) : Option Pattern :=
  placeOf (2 * Mettapedia.GSLT.LanguageDef.RestrictionBlocks.size component + 1) component

/-- Whether a component sits at a place. -/
def placedAt (place component : Pattern) : Bool := placeAt component == some place

mutual
  /-- **A block read back at a place**, as an ambient block over the same restrictions: its components placed there,
  read. -/
  def decodeForm : Nat → Pattern → Prenex → Prenex
    | 0, _, _ => Prenex.nil
    | fuel + 1, place, form => ⟨form.count, readPlaced fuel (liftBVars 0 form.count place) form.components⟩

  /-- **The components placed at a place, read**, in their order: an ambient placed there is read among the
  components placed elsewhere. -/
  def readPlaced : Nat → Pattern → List Pattern → List Pattern
    | 0, _, _ => []
    | fuel + 1, place, components =>
        (components.filter (placedAt place)).map fun component =>
          readComponent fuel place component (components.filter fun other => !placedAt place other)

  /-- **A component read back**, at its place, among the components placed elsewhere. -/
  def readComponent : Nat → Pattern → Pattern → List Pattern → Pattern
    | 0, _, _, _ => inaction
    | fuel + 1, place, .apply label [_, second, third], elsewhere =>
        if label ∈ markers then
          if isVariable third then wrapContent label third (Prenex.body ambientBlock (readPlaced fuel second elsewhere))
          else inaction
        else if label ∈ capabilities then
          if isVariable second then
            .apply (ambientCapability label)
              [second, Prenex.toPattern ambientBlock (decodeForm fuel place (decompose locatedBlock third))]
          else inaction
        else if label = "LCap" then
          if isMessage second then
            .apply "ACap" [second, Prenex.toPattern ambientBlock (decodeForm fuel place (decompose locatedBlock third))]
          else inaction
        else inaction
    | fuel + 1, place, .apply label [_, second], _ =>
        if label ∈ inputs then
          match second with
          | .lambda binder body =>
              .apply (ambientInput label) [.lambda binder (Prenex.toPattern ambientBlock
                (decodeForm fuel (liftBVars 0 1 place) (decompose locatedBlock body)))]
          | _ => inaction
        else if label ∈ outputs then
          if isMessage second then .apply (ambientOutput label) [second] else inaction
        else inaction
    | fuel + 1, place, .apply label [argument], _ =>
        if label = "LRep" then
          .apply "ARep" [Prenex.toPattern ambientBlock (decodeForm fuel place (decompose locatedBlock argument))]
        else inaction
    | _ + 1, _, _, _ => inaction
end

/-- **A located process read back at a place**, within a fuel. -/
def decodeAt (fuel : Nat) (place process : Pattern) : Pattern :=
  Prenex.toPattern ambientBlock (decodeForm fuel place (decompose locatedBlock process))

/-! ## Communication, read back -/

/-- A prefix by a capability term, read: the prefix by its message, its continuation's block read at the place. -/
theorem readComponent_cap {fuel : Nat} {place first capability continuation : Pattern} {elsewhere : List Pattern} :
    readComponent (fuel + 1) place (.apply "LCap" [first, capability, continuation]) elsewhere =
      if isMessage capability then
        .apply "ACap" [capability, decodeAt fuel place continuation]
      else inaction := by
  simp [readComponent, decodeAt]

/-- An input, read: its body's block read at the place, under the binder. -/
theorem readComponent_input {fuel : Nat} {place first body : Pattern} {elsewhere : List Pattern} {label : String}
    {binder : Option String} (isInput : label ∈ inputs) :
    readComponent (fuel + 1) place (.apply label [first, .lambda binder body]) elsewhere =
      .apply (ambientInput label) [.lambda binder (decodeAt fuel (liftBVars 0 1 place) body)] := by
  simp [readComponent, isInput, decodeAt]

/-- No input is an output. -/
theorem not_input_of_output {label : String} (isOutput : label ∈ outputs) : label ∉ inputs := by
  simp only [outputs, List.mem_cons, List.not_mem_nil, or_false] at isOutput
  rcases isOutput with rfl | rfl <;> simp [inputs]

/-- No output is an input. -/
theorem not_output_of_input {label : String} (isInput : label ∈ inputs) : label ∉ outputs := by
  simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at isInput
  rcases isInput with rfl | rfl <;> simp [outputs]

/-- An output, read: its message. -/
theorem readComponent_output {fuel : Nat} {place first message : Pattern} {elsewhere : List Pattern} {label : String}
    (isOutput : label ∈ outputs) :
    readComponent (fuel + 1) place (.apply label [first, message]) elsewhere =
      if isMessage message then .apply (ambientOutput label) [message] else inaction := by
  simp [readComponent, not_input_of_output isOutput, isOutput]

theorem ambientInput_listed {label sort : String} (listed : (label, sort) ∈ [("LInName", "Name"), ("LInCap", "Cap")]) :
    (ambientInput label, sort) ∈ [("AInName", "Name"), ("AInCap", "Cap")] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
  rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [ambientInput]

theorem ambientOutput_listed {label sort : String}
    (listed : (label, sort) ∈ [("LOutName", "Name"), ("LOutCap", "Cap")]) :
    (ambientOutput label, sort) ∈ [("AOutName", "Name"), ("AOutCap", "Cap")] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
  rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [ambientOutput]

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
