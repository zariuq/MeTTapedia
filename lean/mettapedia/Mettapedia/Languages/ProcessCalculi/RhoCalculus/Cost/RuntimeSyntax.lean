import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Wrapping
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Sort

/-!
# Independent executable cost-rho syntax

The raw model is deliberately separate from the declarative inductives.  It
uses canonical lists for signature products and n-ary lists for structural
parallel composition, matching the data traversed by an executable reducer.
Ground authority atoms are strings at this machine-readable boundary.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-- Canonical runtime signature representation. -/
abbrev RawCostSig := List String

/-- Ordered temporal stacks; the first signature is the spendable head. -/
abbrev RawCostStack := List RawCostSig

mutual
  inductive RawCostName where
    | bvar : Nat → RawCostName
    | quote : RawCostTerm → RawCostName
    | signature : RawCostSig → RawCostName
    deriving Repr, DecidableEq

  inductive RawCostProc where
    | nil : RawCostProc
    | par : RawCostProc → RawCostProc → RawCostProc
    | send : RawCostName → RawCostTerm → RawCostProc
    | recv : RawCostName → RawCostTerm → RawCostProc
    deriving Repr, DecidableEq

  inductive RawCostTerm where
    | nil : RawCostTerm
    | signed : RawCostProc → RawCostSig → RawCostTerm
    | par : RawCostTerm → RawCostTerm → RawCostTerm
    | drop : RawCostName → RawCostTerm
    | purse : RawCostName → RawCostStack → RawCostTerm
    deriving Repr, DecidableEq
end

/-- Normalized top-level runtime components. -/
abbrev RawCostConfig := List RawCostTerm

/-- Insert after existing equivalent elements.  Processing a source list from
left to right therefore preserves occurrence order among equal keys. -/
def stableInsertBy {Alpha : Type} (before : Alpha → Alpha → Bool)
    (item : Alpha) : List Alpha → List Alpha
  | [] => [item]
  | head :: tail =>
      if before item head then item :: head :: tail
      else head :: stableInsertBy before item tail

/-- A transparent stable insertion sort used by the executable reference
semantics.  Its simple recursion is intentionally available to kernel proofs. -/
def stableSortBy {Alpha : Type} (before : Alpha → Alpha → Bool)
    (items : List Alpha) : List Alpha :=
  items.foldl (fun sorted item => stableInsertBy before item sorted) []

namespace RawCostSig

/-- Lexicographic canonicalization of the free commutative-monoid carrier. -/
def normalize (sig : RawCostSig) : RawCostSig :=
  stableSortBy (fun left right => decide (left < right)) sig

/-- Runtime signatures are nonempty products of authority atoms. -/
def valid (sig : RawCostSig) : Bool := !sig.isEmpty

/-- Exact multiset subtraction, retaining the canonical order of the minuend. -/
def subtract (available required : RawCostSig) : Option RawCostSig :=
  required.foldlM (fun remaining atom =>
    if atom ∈ remaining then some (remaining.erase atom) else none) available

/-- Exact multiset containment. -/
def contains (available required : RawCostSig) : Bool :=
  (subtract available required).isSome

end RawCostSig

def rawCostSigKey (sig : RawCostSig) : String :=
  "sig(" ++ String.intercalate "," (sig.normalize.map fun atom =>
    toString atom.toUTF8.size ++ ":" ++ atom) ++ ")"

mutual
  /-- Unambiguous structural key for normalized raw names. -/
  def RawCostName.key : RawCostName → String
    | .bvar index => "$" ++ toString index
    | .quote term => "@(" ++ term.key ++ ")"
    | .signature sig => rawCostSigKey sig

  /-- Unambiguous structural key for normalized raw processes. -/
  def RawCostProc.key : RawCostProc → String
    | .nil => "0"
    | .par left right => "par(" ++ left.key ++ "|" ++ right.key ++ ")"
    | .send channel payload =>
        "send(" ++ channel.key ++ "," ++ payload.key ++ ")"
    | .recv channel body =>
        "recv(" ++ channel.key ++ "," ++ body.key ++ ")"

  /-- Unambiguous structural key for normalized raw cost terms. -/
  def RawCostTerm.key : RawCostTerm → String
    | .nil => "tnil"
    | .signed proc sig =>
        "signed(" ++ proc.key ++ "," ++ rawCostSigKey sig ++ ")"
    | .par left right => "tpar(" ++ left.key ++ "|" ++ right.key ++ ")"
    | .drop name => "drop(" ++ name.key ++ ")"
    | .purse surface stack =>
        "purse(" ++ surface.key ++ "," ++
          String.intercalate ";"
            (stack.map rawCostSigKey) ++ ")"
end

/-- Stable sorting by structural key; equal occurrences retain source order. -/
def stableKeySort {Alpha : Type} (key : Alpha → String) (items : List Alpha) : List Alpha :=
  stableSortBy (fun left right => decide (key left < key right)) items

mutual
  /-- Flatten only process parallel composition and erase process nil. -/
  def RawCostProc.components : RawCostProc → List RawCostProc
    | .nil => []
    | .par left right => left.components ++ right.components
    | proc => [proc]

  /-- Flatten only term parallel composition and erase term nil.  Depleted
  purses remain ordinary components. -/
  def RawCostTerm.components : RawCostTerm → List RawCostTerm
    | .nil => []
    | .par left right => left.components ++ right.components
    | term => [term]
end

def RawCostProc.fromComponents : List RawCostProc → RawCostProc
  | [] => .nil
  | [proc] => proc
  | proc :: procs => .par proc (RawCostProc.fromComponents procs)

def RawCostTerm.fromComponents : List RawCostTerm → RawCostTerm
  | [] => .nil
  | [term] => term
  | term :: terms => .par term (RawCostTerm.fromComponents terms)

mutual
  /-- Structural normalization of names. -/
  def RawCostName.normalize : RawCostName → RawCostName
    | .bvar index => .bvar index
    | .quote term =>
        match term.normalize with
        | .drop name => name
        | normalized => .quote normalized
    | .signature sig => .signature sig.normalize

  /-- Structural normalization of process bodies. -/
  def RawCostProc.normalize : RawCostProc → RawCostProc
    | .nil => .nil
    | .par left right =>
        RawCostProc.fromComponents <|
          stableKeySort RawCostProc.key <|
            left.normalize.components ++ right.normalize.components
    | .send channel payload => .send channel.normalize payload.normalize
    | .recv channel body => .recv channel.normalize body.normalize

  /-- Structural normalization of wrapped terms and located purses. -/
  def RawCostTerm.normalize : RawCostTerm → RawCostTerm
    | .nil => .nil
    | .signed proc sig => .signed proc.normalize sig.normalize
    | .par left right =>
        RawCostTerm.fromComponents <|
          stableKeySort RawCostTerm.key <|
            left.normalize.components ++ right.normalize.components
    | .drop name => .drop name.normalize
    | .purse surface stack =>
        .purse surface.normalize (stack.map RawCostSig.normalize)
end

/-- Canonical top-level component list. -/
def RawCostTerm.normalizeConfig (term : RawCostTerm) : RawCostConfig :=
  stableKeySort RawCostTerm.key term.normalize.components

mutual
  def RawCostName.wellFormed : RawCostName → Bool
    | .bvar _ => true
    | .quote term => term.wellFormed
    | .signature sig => sig.valid

  def RawCostProc.wellFormed : RawCostProc → Bool
    | .nil => true
    | .par left right => left.wellFormed && right.wellFormed
    | .send channel payload => channel.wellFormed && payload.wellFormed
    | .recv channel body => channel.wellFormed && body.wellFormed

  def RawCostTerm.wellFormed : RawCostTerm → Bool
    | .nil => true
    | .signed proc sig => proc.wellFormed && sig.valid
    | .par left right => left.wellFormed && right.wellFormed
    | .drop name => name.wellFormed
    | .purse surface stack =>
        surface.wellFormed && stack.all RawCostSig.valid
end

mutual
  /-- Executable scope check for raw names.  A quotation seals its surrounding
  binders and therefore restarts at depth zero. -/
  def RawCostName.binderSafeAt (depth : Nat) : RawCostName → Bool
    | .bvar index => decide (index < depth)
    | .quote term => term.binderSafeAt 0
    | .signature _ => true

  /-- Executable scope check through raw process syntax. -/
  def RawCostProc.binderSafeAt (depth : Nat) : RawCostProc → Bool
    | .nil => true
    | .par left right => left.binderSafeAt depth && right.binderSafeAt depth
    | .send channel payload =>
        channel.binderSafeAt depth && payload.binderSafeAt depth
    | .recv channel body =>
        channel.binderSafeAt depth && body.binderSafeAt (depth + 1)

  /-- Executable scope check through raw cost wrappers.  Purse locations are
  bookkeeping and disappear under pure erasure. -/
  def RawCostTerm.binderSafeAt (depth : Nat) : RawCostTerm → Bool
    | .nil => true
    | .signed process _ => process.binderSafeAt depth
    | .par left right => left.binderSafeAt depth && right.binderSafeAt depth
    | .drop name => name.binderSafeAt depth
    | .purse _ _ => true
end

/-- Top-level executable scope check. -/
def RawCostTerm.binderSafe (term : RawCostTerm) : Bool :=
  term.binderSafeAt 0

mutual
  /-- Runtime scope check for raw names.  Unlike the pure-erasure predicate,
  this descends through every raw field, including purse locations. -/
  def RawCostName.runtimeBinderSafeAt (depth : Nat) : RawCostName → Bool
    | .bvar index => decide (index < depth)
    | .quote term => term.runtimeBinderSafeAt 0
    | .signature _ => true

  /-- Runtime scope check through raw process syntax. -/
  def RawCostProc.runtimeBinderSafeAt (depth : Nat) : RawCostProc → Bool
    | .nil => true
    | .par left right =>
        left.runtimeBinderSafeAt depth && right.runtimeBinderSafeAt depth
    | .send channel payload =>
        channel.runtimeBinderSafeAt depth && payload.runtimeBinderSafeAt depth
    | .recv channel body =>
        channel.runtimeBinderSafeAt depth &&
          body.runtimeBinderSafeAt (depth + 1)

  /-- Whole-object runtime scope check.  Purse locations participate even
  though they disappear under pure erasure. -/
  def RawCostTerm.runtimeBinderSafeAt (depth : Nat) : RawCostTerm → Bool
    | .nil => true
    | .signed process _ => process.runtimeBinderSafeAt depth
    | .par left right =>
        left.runtimeBinderSafeAt depth && right.runtimeBinderSafeAt depth
    | .drop name => name.runtimeBinderSafeAt depth
    | .purse surface _ => surface.runtimeBinderSafeAt depth
end

/-- Top-level whole-object runtime scope check. -/
def RawCostTerm.runtimeBinderSafe (term : RawCostTerm) : Bool :=
  term.runtimeBinderSafeAt 0

/-- Public raw inputs must satisfy both the cost grammar and whole-object
binder scope. -/
def RawCostTerm.supported (term : RawCostTerm) : Bool :=
  term.wellFormed && term.runtimeBinderSafe

example :
    (RawCostTerm.signed
      (.recv (.signature ["x"])
        (.drop (.bvar 0))) ["seal"]).binderSafe = true := by
  decide

example : (RawCostTerm.drop (.bvar 0)).binderSafe = false := by
  decide

/-- A dangling purse location is invisible to pure erasure but rejected at
the public runtime boundary. -/
example :
    (RawCostTerm.purse (.bvar 0) []).binderSafe = true ∧
      (RawCostTerm.purse (.bvar 0) []).runtimeBinderSafe = false := by
  decide

mutual
  def RawCostName.lift (amount cutoff : Nat) : RawCostName → RawCostName
    | .bvar index => if cutoff ≤ index then .bvar (index + amount) else .bvar index
    | .quote term => .quote term
    | .signature sig => .signature sig

  def RawCostProc.lift (amount cutoff : Nat) : RawCostProc → RawCostProc
    | .nil => .nil
    | .par left right => .par (left.lift amount cutoff) (right.lift amount cutoff)
    | .send channel payload => .send (channel.lift amount cutoff) (payload.lift amount cutoff)
    | .recv channel body => .recv (channel.lift amount cutoff) (body.lift amount (cutoff + 1))

  def RawCostTerm.lift (amount cutoff : Nat) : RawCostTerm → RawCostTerm
    | .nil => .nil
    | .signed proc sig => .signed (proc.lift amount cutoff) sig
    | .par left right => .par (left.lift amount cutoff) (right.lift amount cutoff)
    | .drop name => .drop (name.lift amount cutoff)
    | .purse surface stack => .purse (surface.lift amount cutoff) stack
end

mutual
  def RawCostName.substitute (replacement : RawCostTerm) (depth : Nat) :
      RawCostName → RawCostName
    | .bvar index =>
        if index = depth then .quote (replacement.lift depth 0)
        else if depth < index then .bvar (index - 1)
        else .bvar index
    | .quote term => .quote term
    | .signature sig => .signature sig

  def RawCostProc.substitute (replacement : RawCostTerm) (depth : Nat) :
      RawCostProc → RawCostProc
    | .nil => .nil
    | .par left right =>
        .par (RawCostProc.substitute replacement depth left)
          (RawCostProc.substitute replacement depth right)
    | .send channel payload =>
        .send (channel.substitute replacement depth)
          (RawCostTerm.substitute replacement depth payload)
    | .recv channel body =>
        .recv (channel.substitute replacement depth)
          (RawCostTerm.substitute replacement (depth + 1) body)

  def RawCostTerm.substitute (replacement : RawCostTerm) (depth : Nat) :
      RawCostTerm → RawCostTerm
    | .nil => .nil
    | .signed proc sig => .signed (proc.substitute replacement depth) sig
    | .par left right =>
        .par (RawCostTerm.substitute replacement depth left)
          (RawCostTerm.substitute replacement depth right)
    | .drop (.bvar index) =>
        if index = depth then replacement.lift depth 0
        else if depth < index then .drop (.bvar (index - 1))
        else .drop (.bvar index)
    | .drop name => .drop name
    | .purse surface stack => .purse (surface.substitute replacement depth) stack
end

def RawCostTerm.commSubst (body payload : RawCostTerm) : RawCostTerm :=
  RawCostTerm.substitute payload 0 body

/-! ## Typed/raw encoding boundary -/

def encodeCostSig (sig : CostSig String) : RawCostSig :=
  sig.sort (· ≤ ·)

def decodeCostSig (sig : RawCostSig) : CostSig String := sig

mutual
  def encodeCostName : CostName String → RawCostName
    | .bvar index => .bvar index
    | .quote term => .quote (encodeCostTerm term)
    | .signature sig => .signature (encodeCostSig sig)

  def encodeCostProc : CostProc String → RawCostProc
    | .nil => .nil
    | .par left right => .par (encodeCostProc left) (encodeCostProc right)
    | .send channel payload => .send (encodeCostName channel) (encodeCostTerm payload)
    | .recv channel body => .recv (encodeCostName channel) (encodeCostTerm body)

  def encodeCostTerm : CostTerm String → RawCostTerm
    | .nil => .nil
    | .signed proc sig => .signed (encodeCostProc proc) (encodeCostSig sig)
    | .par left right => .par (encodeCostTerm left) (encodeCostTerm right)
    | .drop name => .drop (encodeCostName name)
    | .purse surface stack => .purse (encodeCostName surface) (encodeCostStack stack)

  def encodeCostStack : CostStack String → RawCostStack
    | .empty => []
    | .cons sig rest => encodeCostSig sig :: encodeCostStack rest
end

mutual
  def decodeCostName : RawCostName → CostName String
    | .bvar index => .bvar index
    | .quote term => .quote (decodeCostTerm term)
    | .signature sig => .signature (decodeCostSig sig)

  def decodeCostProc : RawCostProc → CostProc String
    | .nil => .nil
    | .par left right => .par (decodeCostProc left) (decodeCostProc right)
    | .send channel payload => .send (decodeCostName channel) (decodeCostTerm payload)
    | .recv channel body => .recv (decodeCostName channel) (decodeCostTerm body)

  def decodeCostTerm : RawCostTerm → CostTerm String
    | .nil => .nil
    | .signed proc sig => .signed (decodeCostProc proc) (decodeCostSig sig)
    | .par left right => .par (decodeCostTerm left) (decodeCostTerm right)
    | .drop name => .drop (decodeCostName name)
    | .purse surface stack => .purse (decodeCostName surface) (decodeCostStack stack)

  def decodeCostStack : RawCostStack → CostStack String
    | [] => .empty
    | sig :: rest => .cons (decodeCostSig sig) (decodeCostStack rest)
end

@[simp]
theorem decodeCostSig_encodeCostSig (sig : CostSig String) :
    decodeCostSig (encodeCostSig sig) = sig := by
  simp [decodeCostSig, encodeCostSig]

/-! ## Machine-readable wire boundary -/

inductive CostWire where
  | symbol : String → CostWire
  | natural : Nat → CostWire
  | node : String → List CostWire → CostWire
  deriving Repr, Lean.ToJson, Lean.FromJson

namespace CostWire

def encodeSig (sig : RawCostSig) : CostWire :=
  .node "signature" (sig.map CostWire.symbol)

def decodeSig : CostWire → Option RawCostSig
  | .node "signature" atoms => atoms.mapM fun
      | .symbol atom => some atom
      | _ => none
  | _ => none

mutual
  def encodeName : RawCostName → CostWire
    | .bvar index => .node "bvar" [.natural index]
    | .quote term => .node "quote" [encodeTerm term]
    | .signature sig => encodeSig sig

  def encodeProc : RawCostProc → CostWire
    | .nil => .node "proc-nil" []
    | .par left right => .node "proc-par" [encodeProc left, encodeProc right]
    | .send channel payload => .node "send" [encodeName channel, encodeTerm payload]
    | .recv channel body => .node "recv" [encodeName channel, encodeTerm body]

  def encodeTerm : RawCostTerm → CostWire
    | .nil => .node "term-nil" []
    | .signed proc sig => .node "signed" [encodeProc proc, encodeSig sig]
    | .par left right => .node "term-par" [encodeTerm left, encodeTerm right]
    | .drop name => .node "drop" [encodeName name]
    | .purse surface stack =>
        .node "purse" [encodeName surface,
          .node "stack" (stack.map encodeSig)]

  def decodeName : CostWire → Option RawCostName
    | .node "bvar" [.natural index] => some (.bvar index)
    | .node "quote" [term] => .quote <$> decodeTerm term
    | wire => .signature <$> decodeSig wire

  def decodeProc : CostWire → Option RawCostProc
    | .node "proc-nil" [] => some .nil
    | .node "proc-par" [left, right] => .par <$> decodeProc left <*> decodeProc right
    | .node "send" [channel, payload] =>
        .send <$> decodeName channel <*> decodeTerm payload
    | .node "recv" [channel, body] =>
        .recv <$> decodeName channel <*> decodeTerm body
    | _ => none

  def decodeTerm : CostWire → Option RawCostTerm
    | .node "term-nil" [] => some .nil
    | .node "signed" [proc, sig] =>
        .signed <$> decodeProc proc <*> decodeSig sig
    | .node "term-par" [left, right] => .par <$> decodeTerm left <*> decodeTerm right
    | .node "drop" [name] => .drop <$> decodeName name
    | .node "purse" [surface, .node "stack" stack] =>
        .purse <$> decodeName surface <*> stack.mapM decodeSig
    | _ => none
end

end CostWire

/- The raw reference semantics is intentionally kernel-executable across
module boundaries.  This attribute set is the trusted reduction interface used
by closed conformance examples and later bridge proofs. -/
attribute [reducible]
  stableInsertBy stableSortBy
  RawCostSig.normalize RawCostSig.valid RawCostSig.subtract RawCostSig.contains
  rawCostSigKey RawCostName.key RawCostProc.key RawCostTerm.key stableKeySort
  RawCostProc.components RawCostTerm.components RawCostProc.fromComponents
  RawCostTerm.fromComponents RawCostName.normalize RawCostProc.normalize
  RawCostTerm.normalize RawCostTerm.normalizeConfig RawCostName.wellFormed
  RawCostProc.wellFormed RawCostTerm.wellFormed RawCostName.binderSafeAt
  RawCostProc.binderSafeAt RawCostTerm.binderSafeAt RawCostTerm.binderSafe
  RawCostName.runtimeBinderSafeAt RawCostProc.runtimeBinderSafeAt
  RawCostTerm.runtimeBinderSafeAt RawCostTerm.runtimeBinderSafe
  RawCostTerm.supported RawCostName.lift
  RawCostProc.lift RawCostTerm.lift RawCostName.substitute
  RawCostProc.substitute RawCostTerm.substitute RawCostTerm.commSubst

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
