import Mettapedia.Logic.LP.FirstOrderBridge
import Mettapedia.Logic.LP.GroundingSeparation
import Mettapedia.Logic.Saturation.Rewriting

/-!
# Equational rewriting of logic-programming terms

An LP rewrite retains its authored equation, substitution, and single occurrence.
The lossless first-order translation sends these steps to the unrestricted Rw
calculus. Soundness is inherited from that calculus in explicitly chosen models;
an equation's presence in a language or rule collection never implies validity.

The observations here are term denotations and predicate truth. Ordered answers,
duplicate witnesses, execution effects, and runtime costs require separate
interpretations and are not consequences of these first-order laws.

The model matters. In the Herbrand structure a term denotes its own ground
instance, so with two distinct ground terms the only valid equations are
identities and rewriting with valid rules changes nothing
(`rewrite_eq_of_valid_herbrand`). A rewriting law with content, such as
reassociation of relational composition, is a law of a model that is not free.
The statement for Herbrand interpretations themselves is in
`EquationalInterpretations`: rewriting preserves membership in an
interpretation exactly when the interpretation respects the congruence the
rules generate on ground terms.
-/

namespace Mettapedia.Logic.LP.FirstOrderRewriting

open FirstOrderBridge

variable {σ : LPSignature}

/-- One distinguished occurrence of a term in the LP syntax. -/
inductive Context (σ : LPSignature) : Type _ where
  | hole : Context σ
  | app (symbol : σ.functionSymbols) (arguments : Fin (σ.functionArity symbol) → Term σ)
      (position : Fin (σ.functionArity symbol)) (inner : Context σ) : Context σ

def Context.fill : Context σ → Term σ → Term σ
  | .hole, term => term
  | .app symbol arguments position inner, term =>
    .app symbol (Function.update arguments position (inner.fill term))

/-- The context that places `inner` in the hole of `outer`. -/
def Context.comp : Context σ → Context σ → Context σ
  | .hole, inner => inner
  | .app symbol arguments position outer, inner =>
    .app symbol arguments position (outer.comp inner)

@[simp] theorem Context.fill_comp (outer inner : Context σ) (term : Term σ) :
    (outer.comp inner).fill term = outer.fill (inner.fill term) := by
  induction outer with
  | hole => rfl
  | app symbol arguments position outer ih => simp only [Context.comp, Context.fill, ih]

def Context.encode : Context σ → Saturation.Rewriting.Context (language σ) σ.vars
  | .hole => .hole
  | .app symbol arguments position inner =>
    .app (.function symbol) (fun index => encodeTerm (arguments index)) position inner.encode

private def Context.decodeNode : {arity : Nat} → FunctionSymbol σ arity →
    (Fin arity → (language σ).Term σ.vars) → Fin arity → Context σ → Context σ
  | _, .constant _, _, position, _ => Fin.elim0 position
  | _, .function symbol, arguments, position, inner =>
    .app symbol (fun index => decodeTerm (arguments index)) position inner

def Context.decode : Saturation.Rewriting.Context (language σ) σ.vars → Context σ
  | .hole => .hole
  | .app symbol arguments position inner =>
    Context.decodeNode symbol arguments position (Context.decode inner)

@[simp] theorem Context.decode_encode (context : Context σ) : (Context.decode context.encode) = context := by
  induction context with
  | hole => rfl
  | app symbol arguments position inner ih =>
    simp only [Context.encode, Context.decode, Context.decodeNode, decodeTerm_encodeTerm, ih]

@[simp] theorem Context.encode_decode (context : Saturation.Rewriting.Context (language σ) σ.vars) :
    (Context.decode context).encode = context := by
  induction context with
  | hole => rfl
  | app symbol arguments position inner ih =>
    cases symbol with
    | constant => exact Fin.elim0 position
    | function =>
      simp only [Context.decode, Context.decodeNode, Context.encode, encodeTerm_decodeTerm, ih]

def contextEquiv : Context σ ≃ Saturation.Rewriting.Context (language σ) σ.vars where
  toFun := Context.encode
  invFun := Context.decode
  left_inv := Context.decode_encode
  right_inv := Context.encode_decode

@[simp] theorem Context.encode_fill (context : Context σ) (term : Term σ) :
    encodeTerm (context.fill term) = context.encode.fill (encodeTerm term) := by
  induction context with
  | hole => rfl
  | app symbol arguments position inner ih =>
    simp only [Context.fill, Context.encode, encodeTerm, Saturation.Rewriting.Context.fill]
    congr 1
    funext index
    by_cases same : index = position
    · subst index
      simpa only [Function.update_self] using ih
    · simp only [Function.update_of_ne same]

@[simp] theorem Context.decode_fill (context : Saturation.Rewriting.Context (language σ) σ.vars)
    (term : (language σ).Term σ.vars) :
    decodeTerm (context.fill term) = (Context.decode context).fill (decodeTerm term) := by
  apply encodeTerm_injective
  simp only [encodeTerm_decodeTerm, Context.encode_fill, Context.encode_decode]

variable {Model : Type*} [(language σ).Structure Model]

theorem Context.realize_congr (context : Context σ) (assignment : σ.vars → Model)
    {left right : Term σ}
    (same : realizeTerm assignment left = realizeTerm assignment right) :
    realizeTerm assignment (context.fill left) = realizeTerm assignment (context.fill right) := by
  have firstOrder := context.encode.realize_congr assignment
    ((encodeTerm_realize assignment left).trans (same.trans (encodeTerm_realize assignment right).symm))
  simpa only [← Context.encode_fill, encodeTerm_realize] using firstOrder

structure Equation (σ : LPSignature) where
  left : Term σ
  right : Term σ

def Equation.encode (equation : Equation σ) : Saturation.Rewriting.Equation (language σ) σ.vars where
  left := encodeTerm equation.left
  right := encodeTerm equation.right

def Equation.Valid (equation : Equation σ) (Model : Type*) [(language σ).Structure Model] : Prop :=
  ∀ assignment : σ.vars → Model,
    realizeTerm assignment equation.left = realizeTerm assignment equation.right

theorem Equation.encode_valid_iff (equation : Equation σ) :
    equation.encode.Valid Model ↔ equation.Valid Model := by
  simp only [Saturation.Rewriting.Equation.Valid, Equation.encode, Equation.Valid, encodeTerm_realize]

theorem Equation.encode_injective : Function.Injective (Equation.encode (σ := σ)) := by
  intro first second same
  cases first with
  | mk left right =>
    cases second with
    | mk otherLeft otherRight =>
      have leftSame : left = otherLeft := encodeTerm_injective (congrArg Saturation.Rewriting.Equation.left same)
      have rightSame : right = otherRight := encodeTerm_injective (congrArg Saturation.Rewriting.Equation.right same)
      cases leftSame
      cases rightSame
      rfl

/-- Exactly the translated rule collection, without extra target equations. -/
def encodeRules (rules : Set (Equation σ)) : Set (Saturation.Rewriting.Equation (language σ) σ.vars) :=
  Equation.encode '' rules

inductive Rewrite (rules : Set (Equation σ)) : Term σ → Term σ → Prop where
  | rule (equation : Equation σ) (member : equation ∈ rules)
      (substitution : Subst σ) (context : Context σ) :
      Rewrite rules (context.fill (substitution.applyTerm equation.left))
        (context.fill (substitution.applyTerm equation.right))

/-- A rewriting step stays a rewriting step inside a context. -/
theorem Rewrite.inContext {rules : Set (Equation σ)} {left right : Term σ}
    (rewrite : Rewrite rules left right) (outer : Context σ) :
    Rewrite rules (outer.fill left) (outer.fill right) := by
  cases rewrite with
  | rule equation member substitution context =>
    rw [← Context.fill_comp, ← Context.fill_comp]
    exact Rewrite.rule equation member substitution (outer.comp context)

theorem Rewrite.encode {rules : Set (Equation σ)} {left right : Term σ}
    (rewrite : Rewrite rules left right) :
    Saturation.Rewriting.Rewrite (encodeRules rules) (encodeTerm left) (encodeTerm right) := by
  cases rewrite with
  | rule equation member substitution context =>
    rw [Context.encode_fill, Context.encode_fill, encodeTerm_applyTerm, encodeTerm_applyTerm]
    exact Saturation.Rewriting.Rewrite.rule (rules := encodeRules rules) equation.encode
      (Set.mem_image_of_mem Equation.encode member)
      (fun name => encodeTerm (substitution name)) context.encode

theorem Rewrite.decode {rules : Set (Equation σ)}
    {left right : (language σ).Term σ.vars}
    (rewrite : Saturation.Rewriting.Rewrite (encodeRules rules) left right) :
    Rewrite rules (decodeTerm left) (decodeTerm right) := by
  cases rewrite with
  | rule equation member substitution context =>
    obtain ⟨original, member, rfl⟩ := member
    simp only [Context.decode_fill, decodeTerm_subst, Equation.encode, decodeTerm_encodeTerm]
    exact Rewrite.rule original member (fun name => decodeTerm (substitution name)) (Context.decode context)

theorem rewrite_iff_firstOrder {rules : Set (Equation σ)} {left right : Term σ} :
    Rewrite rules left right ↔
      Saturation.Rewriting.Rewrite (encodeRules rules) (encodeTerm left) (encodeTerm right) := by
  constructor
  · exact Rewrite.encode
  · intro rewrite
    simpa only [decodeTerm_encodeTerm] using Rewrite.decode rewrite

/-- Pullback of the public Rw soundness theorem through the LP translation. -/
theorem rewrite_sound {rules : Set (Equation σ)}
    (valid : ∀ equation ∈ rules, equation.Valid Model)
    {left right : Term σ} (rewrite : Rewrite rules left right) (assignment : σ.vars → Model) :
    realizeTerm assignment left = realizeTerm assignment right := by
  have firstOrder := Saturation.Rewriting.rewrite_sound (Model := Model)
    (rules := encodeRules rules) (fun equation member => by
      obtain ⟨original, member, rfl⟩ := member
      exact original.encode_valid_iff.mpr (valid original member)) rewrite.encode assignment
  simpa only [encodeTerm_realize] using firstOrder

inductive Rewrites (rules : Set (Equation σ)) : Term σ → Term σ → Prop where
  | refl (term : Term σ) : Rewrites rules term term
  | step {first middle last : Term σ} (before : Rewrites rules first middle)
      (rewrite : Rewrite rules middle last) : Rewrites rules first last

theorem Rewrites.encode {rules : Set (Equation σ)} {left right : Term σ}
    (derivation : Rewrites rules left right) :
    Saturation.Rewriting.Rewrites (encodeRules rules) (encodeTerm left) (encodeTerm right) := by
  induction derivation with
  | refl => exact Saturation.Rewriting.Rewrites.refl _
  | step _ rewrite ih => exact Saturation.Rewriting.Rewrites.step ih rewrite.encode

theorem Rewrites.decode {rules : Set (Equation σ)}
    {left right : (language σ).Term σ.vars}
    (derivation : Saturation.Rewriting.Rewrites (encodeRules rules) left right) :
    Rewrites rules (decodeTerm left) (decodeTerm right) := by
  induction derivation with
  | refl => exact Rewrites.refl _
  | step _ rewrite ih => exact Rewrites.step ih (Rewrite.decode rewrite)

theorem rewrites_iff_firstOrder {rules : Set (Equation σ)} {left right : Term σ} :
    Rewrites rules left right ↔
      Saturation.Rewriting.Rewrites (encodeRules rules) (encodeTerm left) (encodeTerm right) := by
  constructor
  · exact Rewrites.encode
  · intro derivation
    simpa only [decodeTerm_encodeTerm] using Rewrites.decode derivation

theorem rewrites_sound {rules : Set (Equation σ)}
    (valid : ∀ equation ∈ rules, equation.Valid Model)
    {left right : Term σ} (derivation : Rewrites rules left right) (assignment : σ.vars → Model) :
    realizeTerm assignment left = realizeTerm assignment right := by
  have firstOrder := Saturation.Rewriting.rewrites_sound (Model := Model)
    (rules := encodeRules rules) (fun equation member => by
      obtain ⟨original, member, rfl⟩ := member
      exact original.encode_valid_iff.mpr (valid original member)) derivation.encode assignment
  simpa only [encodeTerm_realize] using firstOrder

/-- Replacing one argument of an atom by a term with the same denotation
preserves its truth. The other arguments stay unchanged. -/
theorem realizeAtom_update_iff (atom : Atom σ) (position : Fin (σ.relationArity atom.symbol))
    (replacement : Term σ) (assignment : σ.vars → Model)
    (equal : realizeTerm assignment (atom.args position) = realizeTerm assignment replacement) :
    realizeAtom assignment atom ↔
      realizeAtom assignment ⟨atom.symbol, Function.update atom.args position replacement⟩ := by
  unfold realizeAtom
  have arguments : (fun index => realizeTerm assignment (atom.args index)) =
      (fun index => realizeTerm assignment (Function.update atom.args position replacement index)) := by
    funext index
    by_cases same : index = position
    · subst index
      simpa only [Function.update_self] using equal
    · simp only [Function.update_of_ne same]
  rw [arguments]

/-- Rewriting at one predicate argument preserves its truth, in any predicate
interpretation of the chosen model. -/
theorem rewrite_atom_iff {rules : Set (Equation σ)}
    (valid : ∀ equation ∈ rules, equation.Valid Model)
    (atom : Atom σ) (position : Fin (σ.relationArity atom.symbol))
    (replacement : Term σ) (rewrite : Rewrite rules (atom.args position) replacement)
    (assignment : σ.vars → Model) :
    realizeAtom assignment atom ↔
      realizeAtom assignment ⟨atom.symbol, Function.update atom.args position replacement⟩ :=
  realizeAtom_update_iff atom position replacement assignment
    (rewrite_sound valid rewrite assignment)

/-- The same for a rewriting sequence. -/
theorem rewrites_atom_iff {rules : Set (Equation σ)}
    (valid : ∀ equation ∈ rules, equation.Valid Model)
    (atom : Atom σ) (position : Fin (σ.relationArity atom.symbol))
    (replacement : Term σ) (derivation : Rewrites rules (atom.args position) replacement)
    (assignment : σ.vars → Model) :
    realizeAtom assignment atom ↔
      realizeAtom assignment ⟨atom.symbol, Function.update atom.args position replacement⟩ :=
  realizeAtom_update_iff atom position replacement assignment
    (rewrites_sound valid derivation assignment)

/-- In the Herbrand structure an equation is valid exactly when its two sides
have the same ground instance under every grounding. -/
theorem Equation.valid_herbrand_iff (interpretation : Interpretation σ)
    (equation : Equation σ) :
    (let := herbrandStructure interpretation
     equation.Valid (GroundTerm σ)) ↔
      ∀ grounding : Grounding σ,
        grounding.groundTerm equation.left = grounding.groundTerm equation.right := by
  dsimp only
  let _ := herbrandStructure interpretation
  constructor
  · intro valid grounding
    exact (realizeTerm_herbrand interpretation grounding _).symm.trans
      ((valid grounding).trans (realizeTerm_herbrand interpretation grounding _))
  · intro same grounding
    exact (realizeTerm_herbrand interpretation grounding _).trans
      ((same grounding).trans (realizeTerm_herbrand interpretation grounding _).symm)

/-- **With two distinct ground terms, an equation valid in the Herbrand
structure is an identity.** -/
theorem Equation.eq_of_valid_herbrand (interpretation : Interpretation σ)
    {first second : GroundTerm σ} (different : first ≠ second) (equation : Equation σ)
    (valid : let := herbrandStructure interpretation
      equation.Valid (GroundTerm σ)) :
    equation.left = equation.right :=
  Grounding.eq_of_groundTerm_eq different
    ((equation.valid_herbrand_iff interpretation).mp valid)

/-- So rewriting with rules valid in the Herbrand structure changes nothing. -/
theorem rewrite_eq_of_valid_herbrand (interpretation : Interpretation σ)
    {first second : GroundTerm σ} (different : first ≠ second)
    {rules : Set (Equation σ)}
    (valid : let := herbrandStructure interpretation
      ∀ equation ∈ rules, equation.Valid (GroundTerm σ))
    {left right : Term σ} (rewrite : Rewrite rules left right) : left = right := by
  cases rewrite with
  | rule equation member substitution context =>
      rw [equation.eq_of_valid_herbrand interpretation different (valid equation member)]

end Mettapedia.Logic.LP.FirstOrderRewriting
