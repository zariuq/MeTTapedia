import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketCertificate

/-! Ordered source packets and the finite declaration facts needed to
recover a physical production from its result sort and constructor label.
The checks concern table data, not assumptions about parser correctness. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketEncoding

open Mettapedia.GSLT.Parsing
open ClassAwareParserPackCorrespondence PresentationExprSemantics
open SourcePacket

def children : List Packet → Packet
  | [] => .symbol "nil"
  | first :: rest => .expression [.symbol "pair", first, children rest]

def structural (label : String) (values : List Packet) : Packet :=
  .expression [.symbol "node", .symbol label, children values]

def lexical (label : String) (point : Nat) : Packet :=
  .expression [.symbol "node", .symbol label, .expression [.symbol "cp", .grounded (.int point)]]

theorem children_read (values : List Packet) : children? (children values) = some values := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp [children, children?, ih]

theorem structural_read (label : String) (values : List Packet) :
    node? (structural label values) = some (label, values) := by
  simp [structural, node?, children_read]

/- Erase spans, retaining the exact constructor tree and scalar spelling.
The singleton terminal case is the scalar action used by lexical rows. -/
mutual
  def encode : CST → Packet
    | .node label _ _ [.terminal [point] _ _] => lexical label point
    | .node label _ _ values => structural label (encodeList values)
    | .terminal values _ _ => children (values.map fun point => .grounded (.int point))

  def encodeList : List CST → List Packet
    | [] => []
    | first :: rest => encode first :: encodeList rest
end

def IsNode : CST → Prop
  | .node _ _ _ _ => True
  | .terminal _ _ _ => False

theorem derivation_isNode {profile : ParserProfileSemantics.ParserProfileLayer}
    {plan : CompiledParserPackPlan} {input : List Nat} {sort : String} {start stop : Nat} {tree : CST}
    (derivation : ParserPackDerivesAt profile plan input sort start stop tree) : IsNode tree := by
  cases derivation <;> trivial

theorem items_are_nodes {profile : ParserProfileSemantics.ParserProfileLayer}
    {plan : CompiledParserPackPlan} {input : List Nat} {items : List PackItem} {start stop : Nat} {values : List CST}
    (derivation : ParserPackItemsDeriveAt profile plan input items start stop values) :
    ∀ tree ∈ values, IsNode tree :=
  match derivation with
  | .nil => by simp
  | .terminal _ rest => items_are_nodes rest
  | .nonterminal head rest => by
    intro tree member
    rcases List.mem_cons.mp member with same | later
    · subst tree; exact derivation_isNode head
    · exact items_are_nodes rest tree later
termination_by structural derivation

theorem encode_structural (label : String) (start stop : Nat) (values : List CST)
    (nodes : ∀ tree ∈ values, IsNode tree) :
    encode (.node label start stop values) = structural label (encodeList values) := by
  cases values with
  | nil => rfl
  | cons first rest =>
    have firstNode := nodes first (List.mem_cons_self)
    cases first with
    | terminal => contradiction
    | node => rfl

def lexicalRows (plan : CompiledParserPackPlan) (sort label : String) :=
  plan.lexical.productions.zipIdx.filter fun (row, _) => row.resultSort == sort && row.label == label

def structuralRows (plan : CompiledParserPackPlan) (sort label : String) :=
  plan.structural.zipIdx.filter fun (row, _) => row.resultSort == sort && row.label == label

/-- Every visible label identifies one physical row. Lexical rows consume
one scalar; an EOF check is a structural item rather than a lexical value. -/
structure Profile (plan : CompiledParserPackPlan) : Prop where
  lexicalRows : ∀ position : Fin plan.lexical.productions.length,
    let row := plan.lexical.productions.get position
    lexicalRows plan row.resultSort row.label = [(row, position.val)]
  lexicalConsumes : ∀ position : Fin plan.lexical.productions.length,
    (plan.lexical.productions.get position).matcher ≠ .eof
  structuralRows : ∀ position : Fin plan.structural.length,
    let row := plan.structural.get position
    structuralRows plan row.resultSort row.label = [(row, position.val)]

def checkProfile (plan : CompiledParserPackPlan) : Bool :=
  (List.finRange plan.lexical.productions.length).all (fun position =>
    let row := plan.lexical.productions.get position
    decide (lexicalRows plan row.resultSort row.label = [(row, position.val)]) && decide (row.matcher ≠ .eof)) &&
  (List.finRange plan.structural.length).all (fun position =>
    let row := plan.structural.get position
    decide (structuralRows plan row.resultSort row.label = [(row, position.val)]))

theorem checkProfile_exact (plan : CompiledParserPackPlan) : checkProfile plan = true ↔ Profile plan := by
  simp only [checkProfile, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_true_left, decide_eq_true_eq]
  constructor
  · rintro ⟨lexical, structural⟩
    exact ⟨fun position => (lexical position).1, fun position => (lexical position).2, structural⟩
  · intro profile
    exact ⟨fun position => ⟨profile.lexicalRows position, profile.lexicalConsumes position⟩,
      profile.structuralRows⟩

open SourcePacketCertificate

theorem propose_lexical (plan : CompiledParserPackPlan) (input : List Nat) (profile : Profile plan)
    (position : Fin plan.lexical.productions.length) (start point fuel : Nat)
    (lookup : input[start]? = some point) :
    proposeFuel plan input (fuel + 1) (plan.lexical.productions.get position).resultSort start
      (lexical (plan.lexical.productions.get position).label point) =
        some (start + 1, .lexical position.val (plan.lexical.productions.get position).matcher start (start + 1)) := by
  have selected := profile.lexicalRows position
  simp only [lexicalRows, List.get_eq_getElem] at selected
  simp [lexical, proposeFuel, lookup, selected]
  rfl

theorem propose_structural (plan : CompiledParserPackPlan) (input : List Nat) (profile : Profile plan)
    (position : Fin plan.structural.length) (start fuel : Nat) (values : List Packet) :
    proposeFuel plan input (fuel + 1) (plan.structural.get position).resultSort start
      (structural (plan.structural.get position).label values) = (do
        let (stop, body, remaining) ← proposeItemsFuel plan input fuel (plan.structural.get position).items start values
        if remaining.isEmpty then pure (stop, .structural position.val start stop body) else none) := by
  have selected := profile.structuralRows position
  simp only [structuralRows, List.get_eq_getElem] at selected
  cases values with
  | nil => simp [structural, children, proposeFuel, node?, children?, selected]; rfl
  | cons first rest => simp [structural, children, proposeFuel, node?, children?, children_read, selected]; rfl

theorem propose_items_nil (plan : CompiledParserPackPlan) (input : List Nat) (fuel start : Nat)
    (values : List Packet) :
    proposeItemsFuel plan input fuel [] start values = some (start, .nil start, values) := by
  rw [proposeItemsFuel]

theorem propose_items_terminal {profile : ParserProfileSemantics.ParserProfileLayer}
    (plan : CompiledParserPackPlan) (input : List Nat) (fuel : Nat) (items : List PackItem)
    {matcher : TerminalMatcher} {start middle : Nat}
    (matched : TerminalMatchesAt profile input matcher start middle) (values : List Packet) :
    proposeItemsFuel plan input fuel (.terminal matcher :: items) start values =
      (proposeItemsFuel plan input fuel items middle values).bind
        (fun (stop, rest, remaining) => some (stop, .terminal matcher start middle rest, remaining)) := by
  cases matched <;> rw [proposeItemsFuel] <;> rfl

theorem propose_items_nonterminal (plan : CompiledParserPackPlan) (input : List Nat) (fuel : Nat)
    (sort : String) (items : List PackItem) (start : Nat) (first : Packet) (rest : List Packet) :
    proposeItemsFuel plan input fuel (.nonterminal sort :: items) start (first :: rest) = (do
      let (middle, head) ← proposeFuel plan input fuel sort start first
      let (stop, body, remaining) ← proposeItemsFuel plan input fuel items middle rest
      pure (stop, .nonterminal sort start middle head body, remaining)) := by
  rw [proposeItemsFuel]

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketEncoding
