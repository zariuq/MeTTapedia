import Mettapedia.Machines.IncrementalConformance.CallableObservationBoundary

/-!
# Matching across the nominal callable boundary

These are independently presented reference and native matching judgments.
They include recursive source expressions, flat/cons patterns, fresh/repeated
pattern variables, and nominal callable leaves. A callable is not an expression
merely because its implementation has neutral Lam code or captured fields.

The correspondence transports successful derivations and their bindings in
both directions, at arbitrary nested positions. Literal callable equality is
the existing nominal/capture observer, not equality of executable bodies.
Source expressions can still contain the ordinary spellings Lam and partial.

This is a first-order observation fragment with explicit variable identities
and closed captured data. It does not prove C execution, runtime tag admission,
foreign attributed-variable hooks, SWI unification of arbitrary open captures,
or extensional function equality. No scheduling or complexity claim is made.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IncrementalConformance.CallableMatchingBoundary

universe u

inductive ReferenceTerm (Value : Type u) where
  | variable (identity : Nat)
  | symbol (name : String)
  | datum (value : Value)
  | expression (elements : List (ReferenceTerm Value))
  | callable (value : NominalCallables.Reference.Callable Value)

inductive NativeTerm (Value : Type u) where
  | variable (identity : Nat)
  | symbol (name : String)
  | datum (value : Value)
  | expression (elements : List (NativeTerm Value))
  | callable (value : NominalCallables.Closure Value)

inductive ReferencePattern (Value : Type u) where
  | bind (identity : Nat)
  | literal (value : ReferenceTerm Value)
  | flat (elements : List (ReferencePattern Value))
  | cons (head tail : ReferencePattern Value)

inductive NativePattern (Value : Type u) where
  | bind (identity : Nat)
  | literal (value : NativeTerm Value)
  | flat (elements : List (NativePattern Value))
  | cons (head tail : NativePattern Value)

mutual
  /-- The relation retains ordinary constructors and ordered expression
  elements, while relating a native code/capture leaf to a reference name. -/
  inductive RelatedTerm {Value : Type u} : ReferenceTerm Value → NativeTerm Value → Prop
    | variable (identity : Nat) : RelatedTerm (.variable identity) (.variable identity)
    | symbol (name : String) : RelatedTerm (.symbol name) (.symbol name)
    | datum (value : Value) : RelatedTerm (.datum value) (.datum value)
    | expression {reference : List (ReferenceTerm Value)} {native : List (NativeTerm Value)} :
        RelatedTerms reference native → RelatedTerm (.expression reference) (.expression native)
    | callable {reference : NominalCallables.Reference.Callable Value}
        {native : NominalCallables.Closure Value} :
        NominalCallables.RelatedValue reference native → RelatedTerm (.callable reference) (.callable native)

  inductive RelatedTerms {Value : Type u} : List (ReferenceTerm Value) → List (NativeTerm Value) → Prop
    | nil : RelatedTerms [] []
    | cons {first : ReferenceTerm Value} {rest : List (ReferenceTerm Value)}
        {nativeFirst : NativeTerm Value} {nativeRest : List (NativeTerm Value)} :
        RelatedTerm first nativeFirst → RelatedTerms rest nativeRest →
        RelatedTerms (first :: rest) (nativeFirst :: nativeRest)
end

mutual
  inductive RelatedPattern {Value : Type u} : ReferencePattern Value → NativePattern Value → Prop
    | bind (identity : Nat) : RelatedPattern (.bind identity) (.bind identity)
    | literal {reference : ReferenceTerm Value} {native : NativeTerm Value} :
        RelatedTerm reference native → RelatedPattern (.literal reference) (.literal native)
    | flat {reference : List (ReferencePattern Value)} {native : List (NativePattern Value)} :
        RelatedPatterns reference native → RelatedPattern (.flat reference) (.flat native)
    | cons {head tail : ReferencePattern Value} {nativeHead nativeTail : NativePattern Value} :
        RelatedPattern head nativeHead → RelatedPattern tail nativeTail →
        RelatedPattern (.cons head tail) (.cons nativeHead nativeTail)

  inductive RelatedPatterns {Value : Type u} :
      List (ReferencePattern Value) → List (NativePattern Value) → Prop
    | nil : RelatedPatterns [] []
    | cons {first : ReferencePattern Value} {rest : List (ReferencePattern Value)}
        {nativeFirst : NativePattern Value} {nativeRest : List (NativePattern Value)} :
        RelatedPattern first nativeFirst → RelatedPatterns rest nativeRest →
        RelatedPatterns (first :: rest) (nativeFirst :: nativeRest)
end

mutual
  /-- Structural data equality with nominal callable equality at leaves. -/
  inductive ReferenceEqual (Value : Type u) [DecidableEq Value] :
      ReferenceTerm Value → ReferenceTerm Value → Prop
    | variable (identity : Nat) : ReferenceEqual Value (.variable identity) (.variable identity)
    | symbol (name : String) : ReferenceEqual Value (.symbol name) (.symbol name)
    | datum (value : Value) : ReferenceEqual Value (.datum value) (.datum value)
    | expression {left right : List (ReferenceTerm Value)} :
        ReferenceListEqual Value left right → ReferenceEqual Value (.expression left) (.expression right)
    | callable {left right : NominalCallables.Reference.Callable Value} :
        NominalCallables.Reference.same left right = true →
        ReferenceEqual Value (.callable left) (.callable right)

  inductive ReferenceListEqual (Value : Type u) [DecidableEq Value] :
      List (ReferenceTerm Value) → List (ReferenceTerm Value) → Prop
    | nil : ReferenceListEqual Value [] []
    | cons {left right : ReferenceTerm Value} {restLeft restRight : List (ReferenceTerm Value)} :
        ReferenceEqual Value left right → ReferenceListEqual Value restLeft restRight →
        ReferenceListEqual Value (left :: restLeft) (right :: restRight)
end

mutual
  /-- Native data equality ignores callable implementation bodies and compares
  the neutral nominal domain plus ordered captures through `NominalCallables.same`. -/
  inductive NativeEqual (Value : Type u) [DecidableEq Value] : NativeTerm Value → NativeTerm Value → Prop
    | variable (identity : Nat) : NativeEqual Value (.variable identity) (.variable identity)
    | symbol (name : String) : NativeEqual Value (.symbol name) (.symbol name)
    | datum (value : Value) : NativeEqual Value (.datum value) (.datum value)
    | expression {left right : List (NativeTerm Value)} :
        NativeListEqual Value left right → NativeEqual Value (.expression left) (.expression right)
    | callable {left right : NominalCallables.Closure Value} :
        NominalCallables.same left right = true → NativeEqual Value (.callable left) (.callable right)

  inductive NativeListEqual (Value : Type u) [DecidableEq Value] :
      List (NativeTerm Value) → List (NativeTerm Value) → Prop
    | nil : NativeListEqual Value [] []
    | cons {left right : NativeTerm Value} {restLeft restRight : List (NativeTerm Value)} :
        NativeEqual Value left right → NativeListEqual Value restLeft restRight →
        NativeListEqual Value (left :: restLeft) (right :: restRight)
end

/-- The nominal comparison law also holds for related noncanonical native
closures, so correspondence does not require equal implementation bodies. -/
theorem callable_comparison_correspondence {Value : Type u} [DecidableEq Value]
    (left right : NominalCallables.Reference.Callable Value)
    (nativeLeft nativeRight : NominalCallables.Closure Value)
    (relatedLeft : NominalCallables.RelatedValue left nativeLeft)
    (relatedRight : NominalCallables.RelatedValue right nativeRight) :
    NominalCallables.same nativeLeft nativeRight = NominalCallables.Reference.same left right := by
  have nominal : NominalCallables.nominalDomain (NominalCallables.Reference.name left) =
      NominalCallables.nominalDomain (NominalCallables.Reference.name right) ↔
      NominalCallables.Reference.name left = NominalCallables.Reference.name right :=
    ⟨fun equal => NominalCallables.nominalDomain_injective equal,
      congrArg NominalCallables.nominalDomain⟩
  have reference : NominalCallables.Reference.same left right =
      decide (NominalCallables.Reference.name left = NominalCallables.Reference.name right ∧
        NominalCallables.Reference.captures left = NominalCallables.Reference.captures right) := by
    cases left <;> cases right <;>
      simp [NominalCallables.Reference.same, NominalCallables.Reference.name,
        NominalCallables.Reference.captures]
  simp only [NominalCallables.same, relatedLeft.1, relatedRight.1,
    relatedLeft.2, relatedRight.2, nominal, reference]

theorem equality_forth {Value : Type u} [DecidableEq Value]
    {left right : ReferenceTerm Value} {nativeLeft nativeRight : NativeTerm Value}
    (equal : ReferenceEqual Value left right)
    (relatedLeft : RelatedTerm left nativeLeft) (relatedRight : RelatedTerm right nativeRight) :
    NativeEqual Value nativeLeft nativeRight := by
  induction equal using ReferenceEqual.rec
      (motive_2 := fun left right _ => ∀ {nativeLeft nativeRight},
        RelatedTerms left nativeLeft → RelatedTerms right nativeRight →
        NativeListEqual Value nativeLeft nativeRight)
      generalizing nativeLeft nativeRight with
  | «variable» identity => cases relatedLeft; cases relatedRight; exact .variable identity
  | symbol name => cases relatedLeft; cases relatedRight; exact .symbol name
  | datum value => cases relatedLeft; cases relatedRight; exact .datum value
  | expression equal ih =>
      cases relatedLeft with
      | expression relatedLeft =>
          cases relatedRight with
          | expression relatedRight => exact .expression (ih relatedLeft relatedRight)
  | callable equal =>
      cases relatedLeft with
      | callable relatedLeft =>
          cases relatedRight with
          | callable relatedRight =>
              exact .callable ((callable_comparison_correspondence _ _ _ _ relatedLeft relatedRight).trans equal)
  | nil =>
      rename_i nativeLeft nativeRight relatedLeft relatedRight
      cases relatedLeft
      cases relatedRight
      exact .nil
  | cons first rest ihFirst ihRest =>
      rename_i nativeLeft nativeRight relatedLeft relatedRight
      cases relatedLeft with
      | cons relatedLeft restLeft =>
          cases relatedRight with
          | cons relatedRight restRight =>
              exact .cons (ihFirst relatedLeft relatedRight) (ihRest restLeft restRight)

theorem list_equality_forth {Value : Type u} [DecidableEq Value]
    {left right : List (ReferenceTerm Value)} {nativeLeft nativeRight : List (NativeTerm Value)}
    (equal : ReferenceListEqual Value left right)
    (relatedLeft : RelatedTerms left nativeLeft) (relatedRight : RelatedTerms right nativeRight) :
    NativeListEqual Value nativeLeft nativeRight := by
  have whole := equality_forth (.expression equal) (.expression relatedLeft) (.expression relatedRight)
  cases whole with
  | expression equal => exact equal

theorem equality_back {Value : Type u} [DecidableEq Value]
    {left right : ReferenceTerm Value} {nativeLeft nativeRight : NativeTerm Value}
    (equal : NativeEqual Value nativeLeft nativeRight)
    (relatedLeft : RelatedTerm left nativeLeft) (relatedRight : RelatedTerm right nativeRight) :
    ReferenceEqual Value left right := by
  induction equal using NativeEqual.rec
      (motive_2 := fun nativeLeft nativeRight _ => ∀ {left right},
        RelatedTerms left nativeLeft → RelatedTerms right nativeRight →
        ReferenceListEqual Value left right)
      generalizing left right with
  | «variable» identity => cases relatedLeft; cases relatedRight; exact .variable identity
  | symbol name => cases relatedLeft; cases relatedRight; exact .symbol name
  | datum value => cases relatedLeft; cases relatedRight; exact .datum value
  | expression equal ih =>
      cases relatedLeft with
      | expression relatedLeft =>
          cases relatedRight with
          | expression relatedRight => exact .expression (ih relatedLeft relatedRight)
  | callable equal =>
      cases relatedLeft with
      | callable relatedLeft =>
          cases relatedRight with
          | callable relatedRight =>
              exact .callable ((callable_comparison_correspondence _ _ _ _ relatedLeft relatedRight).symm.trans equal)
  | nil =>
      rename_i left right relatedLeft relatedRight
      cases relatedLeft
      cases relatedRight
      exact .nil
  | cons first rest ihFirst ihRest =>
      rename_i left right relatedLeft relatedRight
      cases relatedLeft with
      | cons relatedLeft restLeft =>
          cases relatedRight with
          | cons relatedRight restRight =>
              exact .cons (ihFirst relatedLeft relatedRight) (ihRest restLeft restRight)

theorem list_equality_back {Value : Type u} [DecidableEq Value]
    {left right : List (ReferenceTerm Value)} {nativeLeft nativeRight : List (NativeTerm Value)}
    (equal : NativeListEqual Value nativeLeft nativeRight)
    (relatedLeft : RelatedTerms left nativeLeft) (relatedRight : RelatedTerms right nativeRight) :
    ReferenceListEqual Value left right := by
  have whole := equality_back (.expression equal) (.expression relatedLeft) (.expression relatedRight)
  cases whole with
  | expression equal => exact equal

abbrev ReferenceBindings (Value : Type u) := List (Nat × ReferenceTerm Value)
abbrev NativeBindings (Value : Type u) := List (Nat × NativeTerm Value)

namespace Reference

def lookup {Value : Type u} (identity : Nat) : ReferenceBindings Value → Option (ReferenceTerm Value)
  | [] => none
  | (key, value) :: rest => if identity = key then some value else lookup identity rest

end Reference

namespace Native

def lookup {Value : Type u} (identity : Nat) : NativeBindings Value → Option (NativeTerm Value)
  | [] => none
  | (key, value) :: rest => if key = identity then some value else lookup identity rest

end Native

inductive RelatedBindings {Value : Type u} : ReferenceBindings Value → NativeBindings Value → Prop
  | nil : RelatedBindings [] []
  | cons {identity : Nat} {reference : ReferenceTerm Value} {native : NativeTerm Value}
      {restReference : ReferenceBindings Value} {restNative : NativeBindings Value} :
      RelatedTerm reference native → RelatedBindings restReference restNative →
      RelatedBindings ((identity, reference) :: restReference) ((identity, native) :: restNative)

inductive RelatedLookup {Value : Type u} :
    Option (ReferenceTerm Value) → Option (NativeTerm Value) → Prop
  | none : RelatedLookup none none
  | some {reference : ReferenceTerm Value} {native : NativeTerm Value} :
      RelatedTerm reference native → RelatedLookup (some reference) (some native)

theorem lookup_correspondence {Value : Type u} (identity : Nat)
    {reference : ReferenceBindings Value} {native : NativeBindings Value}
    (related : RelatedBindings reference native) :
    RelatedLookup (Reference.lookup identity reference) (Native.lookup identity native) := by
  induction related with
  | nil => exact .none
  | @cons key reference native restReference restNative value rest ih =>
      by_cases equal : identity = key
      · simp only [Reference.lookup, Native.lookup, equal, ↓reduceIte]
        exact .some value
      · simp only [Reference.lookup, Native.lookup, equal, Ne.symm equal, ↓reduceIte]
        exact ih

theorem lookup_none_forth {Value : Type u} (identity : Nat)
    {reference : ReferenceBindings Value} {native : NativeBindings Value}
    (related : RelatedBindings reference native) (absent : Reference.lookup identity reference = none) :
    Native.lookup identity native = none := by
  have lookup := lookup_correspondence identity related
  rw [absent] at lookup
  generalize Native.lookup identity native = found at lookup ⊢
  cases lookup
  rfl

theorem lookup_some_forth {Value : Type u} (identity : Nat)
    {reference : ReferenceBindings Value} {native : NativeBindings Value} {value : ReferenceTerm Value}
    (related : RelatedBindings reference native) (present : Reference.lookup identity reference = some value) :
    ∃ nativeValue, Native.lookup identity native = some nativeValue ∧ RelatedTerm value nativeValue := by
  have lookup := lookup_correspondence identity related
  rw [present] at lookup
  generalize Native.lookup identity native = found at lookup ⊢
  cases lookup with
  | some related => exact ⟨_, rfl, related⟩

theorem lookup_none_back {Value : Type u} (identity : Nat)
    {reference : ReferenceBindings Value} {native : NativeBindings Value}
    (related : RelatedBindings reference native) (absent : Native.lookup identity native = none) :
    Reference.lookup identity reference = none := by
  have lookup := lookup_correspondence identity related
  rw [absent] at lookup
  generalize Reference.lookup identity reference = found at lookup ⊢
  cases lookup
  rfl

theorem lookup_some_back {Value : Type u} (identity : Nat)
    {reference : ReferenceBindings Value} {native : NativeBindings Value} {value : NativeTerm Value}
    (related : RelatedBindings reference native) (present : Native.lookup identity native = some value) :
    ∃ referenceValue, Reference.lookup identity reference = some referenceValue ∧ RelatedTerm referenceValue value := by
  have lookup := lookup_correspondence identity related
  rw [present] at lookup
  generalize Reference.lookup identity reference = found at lookup ⊢
  cases lookup with
  | some related => exact ⟨_, rfl, related⟩

mutual
  inductive ReferenceMatch (Value : Type u) [DecidableEq Value] :
      ReferencePattern Value → ReferenceTerm Value → ReferenceBindings Value → ReferenceBindings Value → Prop
    | fresh {identity : Nat} {value : ReferenceTerm Value} {before : ReferenceBindings Value} :
        Reference.lookup identity before = none →
        ReferenceMatch Value (.bind identity) value before ((identity, value) :: before)
    | existing {identity : Nat} {value old : ReferenceTerm Value} {before : ReferenceBindings Value} :
        Reference.lookup identity before = some old → ReferenceEqual Value old value →
        ReferenceMatch Value (.bind identity) value before before
    | literal {wanted value : ReferenceTerm Value} {before : ReferenceBindings Value} :
        ReferenceEqual Value wanted value → ReferenceMatch Value (.literal wanted) value before before
    | flat {patterns : List (ReferencePattern Value)} {values : List (ReferenceTerm Value)}
        {before after : ReferenceBindings Value} :
        ReferenceMatchMany Value patterns values before after →
        ReferenceMatch Value (.flat patterns) (.expression values) before after
    | cons {head tail : ReferencePattern Value} {first : ReferenceTerm Value}
        {rest : List (ReferenceTerm Value)} {before middle after : ReferenceBindings Value} :
        ReferenceMatch Value head first before middle →
        ReferenceMatch Value tail (.expression rest) middle after →
        ReferenceMatch Value (.cons head tail) (.expression (first :: rest)) before after

  inductive ReferenceMatchMany (Value : Type u) [DecidableEq Value] :
      List (ReferencePattern Value) → List (ReferenceTerm Value) →
      ReferenceBindings Value → ReferenceBindings Value → Prop
    | nil {before : ReferenceBindings Value} : ReferenceMatchMany Value [] [] before before
    | next {pattern : ReferencePattern Value} {patterns : List (ReferencePattern Value)}
        {value : ReferenceTerm Value} {values : List (ReferenceTerm Value)}
        {before middle after : ReferenceBindings Value} :
        ReferenceMatch Value pattern value before middle →
        ReferenceMatchMany Value patterns values middle after →
        ReferenceMatchMany Value (pattern :: patterns) (value :: values) before after
end

mutual
  inductive NativeMatch (Value : Type u) [DecidableEq Value] :
      NativePattern Value → NativeTerm Value → NativeBindings Value → NativeBindings Value → Prop
    | fresh {identity : Nat} {value : NativeTerm Value} {before : NativeBindings Value} :
        Native.lookup identity before = none →
        NativeMatch Value (.bind identity) value before ((identity, value) :: before)
    | existing {identity : Nat} {value old : NativeTerm Value} {before : NativeBindings Value} :
        Native.lookup identity before = some old → NativeEqual Value old value →
        NativeMatch Value (.bind identity) value before before
    | literal {wanted value : NativeTerm Value} {before : NativeBindings Value} :
        NativeEqual Value wanted value → NativeMatch Value (.literal wanted) value before before
    | flat {patterns : List (NativePattern Value)} {values : List (NativeTerm Value)}
        {before after : NativeBindings Value} :
        NativeMatchMany Value patterns values before after →
        NativeMatch Value (.flat patterns) (.expression values) before after
    | cons {head tail : NativePattern Value} {first : NativeTerm Value}
        {rest : List (NativeTerm Value)} {before middle after : NativeBindings Value} :
        NativeMatch Value head first before middle →
        NativeMatch Value tail (.expression rest) middle after →
        NativeMatch Value (.cons head tail) (.expression (first :: rest)) before after

  inductive NativeMatchMany (Value : Type u) [DecidableEq Value] :
      List (NativePattern Value) → List (NativeTerm Value) →
      NativeBindings Value → NativeBindings Value → Prop
    | nil {before : NativeBindings Value} : NativeMatchMany Value [] [] before before
    | next {pattern : NativePattern Value} {patterns : List (NativePattern Value)}
        {value : NativeTerm Value} {values : List (NativeTerm Value)}
        {before middle after : NativeBindings Value} :
        NativeMatch Value pattern value before middle →
        NativeMatchMany Value patterns values middle after →
        NativeMatchMany Value (pattern :: patterns) (value :: values) before after
end

/-- Every successful reference derivation has a native derivation with related
bindings. The induction includes all expression depths, repeated variables,
and the intermediate environments of cons/flat decomposition. -/
theorem matching_forth {Value : Type u} [DecidableEq Value]
    {pattern : ReferencePattern Value} {value : ReferenceTerm Value}
    {before after : ReferenceBindings Value}
    {nativePattern : NativePattern Value} {nativeValue : NativeTerm Value} {nativeBefore : NativeBindings Value}
    (matched : ReferenceMatch Value pattern value before after)
    (patterns : RelatedPattern pattern nativePattern) (values : RelatedTerm value nativeValue)
    (bindings : RelatedBindings before nativeBefore) :
    ∃ nativeAfter, NativeMatch Value nativePattern nativeValue nativeBefore nativeAfter ∧
      RelatedBindings after nativeAfter := by
  induction matched using ReferenceMatch.rec
      (motive_2 := fun patterns values before after _ =>
        ∀ {nativePatterns nativeValues nativeBefore},
          RelatedPatterns patterns nativePatterns → RelatedTerms values nativeValues →
          RelatedBindings before nativeBefore →
          ∃ nativeAfter, NativeMatchMany Value nativePatterns nativeValues nativeBefore nativeAfter ∧
            RelatedBindings after nativeAfter)
      generalizing nativePattern nativeValue nativeBefore with
  | fresh absent =>
      cases patterns with
      | bind =>
          exact ⟨_, .fresh (lookup_none_forth _ bindings absent), .cons values bindings⟩
  | existing present equal =>
      cases patterns with
      | bind =>
          obtain ⟨nativeOld, presentNative, relatedOld⟩ := lookup_some_forth _ bindings present
          exact ⟨_, .existing presentNative (equality_forth equal relatedOld values), bindings⟩
  | literal equal =>
      cases patterns with
      | literal wanted => exact ⟨_, .literal (equality_forth equal wanted values), bindings⟩
  | flat matched ih =>
      cases patterns with
      | flat patterns =>
          cases values with
          | expression values =>
              obtain ⟨nativeAfter, matchedNative, after⟩ := ih patterns values bindings
              exact ⟨nativeAfter, .flat matchedNative, after⟩
  | cons head tail ihHead ihTail =>
      cases patterns with
      | cons headPattern tailPattern =>
          cases values with
          | expression values =>
              cases values with
              | cons first rest =>
                  obtain ⟨nativeMiddle, headNative, middle⟩ := ihHead headPattern first bindings
                  obtain ⟨nativeAfter, tailNative, after⟩ := ihTail tailPattern (.expression rest) middle
                  exact ⟨nativeAfter, .cons headNative tailNative, after⟩
  | nil =>
      rename_i nativePatterns nativeValues nativeBefore patterns values bindings
      cases patterns
      cases values
      exact ⟨_, .nil, bindings⟩
  | next first rest ihFirst ihRest =>
      rename_i nativePatterns nativeValues nativeBefore patterns values bindings
      cases patterns with
      | cons firstPattern restPatterns =>
          cases values with
          | cons firstValue restValues =>
              obtain ⟨nativeMiddle, firstNative, middle⟩ := ihFirst firstPattern firstValue bindings
              obtain ⟨nativeAfter, restNative, after⟩ := ihRest restPatterns restValues middle
              exact ⟨nativeAfter, .next firstNative restNative, after⟩

/-- Successful native matching cannot gain a match by inspecting hidden code.
Its corresponding reference derivation retains every produced binding. -/
theorem matching_back {Value : Type u} [DecidableEq Value]
    {pattern : ReferencePattern Value} {value : ReferenceTerm Value} {before : ReferenceBindings Value}
    {nativePattern : NativePattern Value} {nativeValue : NativeTerm Value}
    {nativeBefore nativeAfter : NativeBindings Value}
    (matched : NativeMatch Value nativePattern nativeValue nativeBefore nativeAfter)
    (patterns : RelatedPattern pattern nativePattern) (values : RelatedTerm value nativeValue)
    (bindings : RelatedBindings before nativeBefore) :
    ∃ after, ReferenceMatch Value pattern value before after ∧ RelatedBindings after nativeAfter := by
  induction matched using NativeMatch.rec
      (motive_2 := fun nativePatterns nativeValues nativeBefore nativeAfter _ =>
        ∀ {patterns values before},
          RelatedPatterns patterns nativePatterns → RelatedTerms values nativeValues →
          RelatedBindings before nativeBefore →
          ∃ after, ReferenceMatchMany Value patterns values before after ∧ RelatedBindings after nativeAfter)
      generalizing pattern value before with
  | fresh absent =>
      cases patterns with
      | bind =>
          exact ⟨_, .fresh (lookup_none_back _ bindings absent), .cons values bindings⟩
  | existing present equal =>
      cases patterns with
      | bind =>
          obtain ⟨old, presentReference, relatedOld⟩ := lookup_some_back _ bindings present
          exact ⟨_, .existing presentReference (equality_back equal relatedOld values), bindings⟩
  | literal equal =>
      cases patterns with
      | literal wanted => exact ⟨_, .literal (equality_back equal wanted values), bindings⟩
  | flat matched ih =>
      cases patterns with
      | flat patterns =>
          cases values with
          | expression values =>
              obtain ⟨after, matchedReference, relatedAfter⟩ := ih patterns values bindings
              exact ⟨after, .flat matchedReference, relatedAfter⟩
  | cons head tail ihHead ihTail =>
      cases patterns with
      | cons headPattern tailPattern =>
          cases values with
          | expression values =>
              cases values with
              | cons first rest =>
                  obtain ⟨middle, headReference, relatedMiddle⟩ := ihHead headPattern first bindings
                  obtain ⟨after, tailReference, relatedAfter⟩ := ihTail tailPattern (.expression rest) relatedMiddle
                  exact ⟨after, .cons headReference tailReference, relatedAfter⟩
  | nil =>
      rename_i patterns values before relatedPatterns relatedValues bindings
      cases relatedPatterns
      cases relatedValues
      exact ⟨_, .nil, bindings⟩
  | next first rest ihFirst ihRest =>
      rename_i patterns values before relatedPatterns relatedValues bindings
      cases relatedPatterns with
      | cons firstPattern restPatterns =>
          cases relatedValues with
          | cons firstValue restValues =>
              obtain ⟨middle, firstReference, relatedMiddle⟩ := ihFirst firstPattern firstValue bindings
              obtain ⟨after, restReference, relatedAfter⟩ := ihRest restPatterns restValues relatedMiddle
              exact ⟨after, .next firstReference restReference, relatedAfter⟩

theorem matching_exists_iff {Value : Type u} [DecidableEq Value]
    {pattern : ReferencePattern Value} {value : ReferenceTerm Value} {before : ReferenceBindings Value}
    {nativePattern : NativePattern Value} {nativeValue : NativeTerm Value} {nativeBefore : NativeBindings Value}
    (patterns : RelatedPattern pattern nativePattern) (values : RelatedTerm value nativeValue)
    (bindings : RelatedBindings before nativeBefore) :
    (∃ after, ReferenceMatch Value pattern value before after) ↔
      (∃ nativeAfter, NativeMatch Value nativePattern nativeValue nativeBefore nativeAfter) := by
  constructor
  · rintro ⟨after, matched⟩
    obtain ⟨nativeAfter, nativeMatch, _⟩ := matching_forth matched patterns values bindings
    exact ⟨nativeAfter, nativeMatch⟩
  · rintro ⟨nativeAfter, matched⟩
    obtain ⟨after, referenceMatch, _⟩ := matching_back matched patterns values bindings
    exact ⟨after, referenceMatch⟩

theorem reference_flat_cannot_unpack_callable {Value : Type u} [DecidableEq Value]
    (patterns : List (ReferencePattern Value)) (callable : NominalCallables.Reference.Callable Value)
    (before after : ReferenceBindings Value) :
    ¬ ReferenceMatch Value (.flat patterns) (.callable callable) before after := by
  intro matched
  cases matched

theorem native_flat_cannot_unpack_callable {Value : Type u} [DecidableEq Value]
    (patterns : List (NativePattern Value)) (closure : NominalCallables.Closure Value)
    (before after : NativeBindings Value) :
    ¬ NativeMatch Value (.flat patterns) (.callable closure) before after := by
  intro matched
  cases matched

theorem reference_cons_cannot_unpack_callable {Value : Type u} [DecidableEq Value]
    (head tail : ReferencePattern Value) (callable : NominalCallables.Reference.Callable Value)
    (before after : ReferenceBindings Value) :
    ¬ ReferenceMatch Value (.cons head tail) (.callable callable) before after := by
  intro matched
  cases matched

theorem native_cons_cannot_unpack_callable {Value : Type u} [DecidableEq Value]
    (head tail : NativePattern Value) (closure : NominalCallables.Closure Value)
    (before after : NativeBindings Value) :
    ¬ NativeMatch Value (.cons head tail) (.callable closure) before after := by
  intro matched
  cases matched

theorem variable_binds_whole_callable {Value : Type u} [DecidableEq Value]
    (identity : Nat) (closure : NominalCallables.Closure Value) :
    NativeMatch Value (.bind identity) (.callable closure) [] [(identity, .callable closure)] :=
  .fresh rfl

/-- Preparing actual source occurrences supplies an admitted expression of
callable leaves. This is derived from the existing independent translator and
native preparation, rather than assuming that their resulting bundles relate. -/
theorem prepared_callable_bundle_related {Value : Type u} (counter : Nat)
    (sources : List NominalCallables.Declaration) (environment : Nat → Value) :
    RelatedTerm
      (.expression (((NominalCallables.Reference.translate counter sources).map
        (NominalCallables.Reference.instantiate environment)).map ReferenceTerm.callable))
      (.expression (((NominalCallables.prepare counter sources).2.map
        (NominalCallables.instantiate environment)).map NativeTerm.callable)) := by
  apply RelatedTerm.expression
  have mapped : ∀ (references : List (NominalCallables.Reference.Callable Value))
      (natives : List (NominalCallables.Closure Value)),
      List.Forall₂ NominalCallables.RelatedValue references natives →
      RelatedTerms (references.map ReferenceTerm.callable) (natives.map NativeTerm.callable) := by
    intro references natives supplied
    induction supplied with
    | nil => exact .nil
    | cons first rest ih => exact .cons (.callable first) ih
  exact mapped _ _ (NominalCallables.prepared_values_related counter sources environment)

theorem binder_patterns_related {Value : Type u} (identities : List Nat) :
    RelatedPattern
      (.flat (identities.map ReferencePattern.bind) : ReferencePattern Value)
      (.flat (identities.map NativePattern.bind) : NativePattern Value) := by
  apply RelatedPattern.flat
  induction identities with
  | nil => exact .nil
  | cons first rest ih => exact .cons (.bind first) ih

/-- Existential matching of a completely prepared bundle agrees for every
binding-pattern catalogue, including repeated identities. -/
theorem prepared_bundle_matching_iff {Value : Type u} [DecidableEq Value]
    (counter : Nat) (sources : List NominalCallables.Declaration) (environment : Nat → Value)
    (identities : List Nat) :
    (∃ after, ReferenceMatch Value (.flat (identities.map ReferencePattern.bind))
      (.expression (((NominalCallables.Reference.translate counter sources).map
        (NominalCallables.Reference.instantiate environment)).map ReferenceTerm.callable)) [] after) ↔
    (∃ after, NativeMatch Value (.flat (identities.map NativePattern.bind))
      (.expression (((NominalCallables.prepare counter sources).2.map
        (NominalCallables.instantiate environment)).map NativeTerm.callable)) [] after) :=
  matching_exists_iff (binder_patterns_related identities)
    (prepared_callable_bundle_related counter sources environment) .nil

/-- A deliberately incorrect executable matcher: it treats a callable's code
children as ordinary public list fields. Its control below demonstrates the
additional match that this representation leak would accept. -/
def exposedCodeFlatAccepts {Value : Type u} (arity : Nat)
    (closure : NominalCallables.Closure Value) : Bool :=
  match closure.code with
  | .apply _ fields => decide (fields.length + 1 = arity)
  | _ => false

theorem exposed_code_forges_flat_match {Value : Type u} [DecidableEq Value]
    (token : Nat) (source : NominalCallables.Declaration) (captures : List Value) :
    exposedCodeFlatAccepts 3 (NominalCallables.close token source captures) = true ∧
    ¬ ∃ after, NativeMatch Value (.flat [.bind 0, .bind 1, .bind 2])
      (.callable (NominalCallables.close token source captures)) [] after := by
  constructor
  · simp [exposedCodeFlatAccepts, NominalCallables.close, NominalCallables.canonical]
  · rintro ⟨after, matched⟩
    exact native_flat_cannot_unpack_callable _ _ [] after matched

namespace Controls

def source : NominalCallables.Declaration := ⟨["x"], .bvar 0, []⟩
def alternateBody : NominalCallables.Declaration := ⟨["z"], .apply "other" [.bvar 0], []⟩
def captured : NominalCallables.Closure Nat := NominalCallables.close 1 source [42]

theorem variable_retains_complete_capture :
    NativeMatch Nat (.bind 7) (.callable captured) [] [(7, .callable captured)] :=
  variable_binds_whole_callable 7 captured

theorem nested_variable_retains_callable :
    NativeMatch Nat (.flat [.literal (.symbol "outer"), .flat [.bind 7]])
      (.expression [.symbol "outer", .expression [.callable captured]]) [] [(7, .callable captured)] := by
  exact .flat (.next (.literal (.symbol "outer"))
    (.next (.flat (.next (.fresh rfl) .nil)) .nil))

theorem nested_cons_cannot_unpack_callable :
    ¬ ∃ after, NativeMatch Nat
      (.flat [.literal (.symbol "outer"), .cons (.bind 0) (.bind 1)])
      (.expression [.symbol "outer", .callable captured]) [] after := by
  rintro ⟨after, matched⟩
  cases matched with
  | flat outer =>
      cases outer with
      | next first rest =>
          cases rest with
          | next inner rest => cases inner

theorem bare_and_captured_both_reject_cons :
    (¬ ∃ after, NativeMatch Nat (.cons (.bind 0) (.bind 1))
      (.callable (NominalCallables.close 1 source [])) [] after) ∧
    (¬ ∃ after, NativeMatch Nat (.cons (.bind 0) (.bind 1)) (.callable captured) [] after) := by
  constructor <;> rintro ⟨after, matched⟩ <;> cases matched

theorem identical_bodies_distinct_tokens_do_not_literal_match :
    ¬ ∃ after, NativeMatch Nat (.literal (.callable (NominalCallables.close 1 source [])))
      (.callable (NominalCallables.close 2 source [])) [] after := by
  rintro ⟨after, matched⟩
  cases matched with
  | literal equal =>
      cases equal with
      | callable equal => simp [NominalCallables.same_close] at equal

theorem same_token_and_captures_ignore_body_representation :
    NativeMatch Nat (.literal (.callable (NominalCallables.close 1 source [42])))
      (.callable (NominalCallables.close 1 alternateBody [42])) [] [] := by
  apply NativeMatch.literal
  apply NativeEqual.callable
  simp [NominalCallables.same_close]

theorem changed_capture_prevents_literal_match :
    ¬ ∃ after, NativeMatch Nat (.literal (.callable (NominalCallables.close 1 source [42])))
      (.callable (NominalCallables.close 1 source [43])) [] after := by
  rintro ⟨after, matched⟩
  cases matched with
  | literal equal =>
      cases equal with
      | callable equal => simp [NominalCallables.same_close] at equal

theorem ordered_captures_prevent_literal_match :
    ¬ ∃ after, NativeMatch Nat (.literal (.callable (NominalCallables.close 1 source [42, 43])))
      (.callable (NominalCallables.close 1 source [43, 42])) [] after := by
  rintro ⟨after, matched⟩
  cases matched with
  | literal equal =>
      cases equal with
      | callable equal => simp [NominalCallables.same_close] at equal

theorem repeated_variable_matches_same_nominal_value :
    NativeMatch Nat (.flat [.bind 0, .bind 0])
      (.expression [.callable (NominalCallables.close 1 source [42]),
        .callable (NominalCallables.close 1 alternateBody [42])]) []
      [(0, .callable (NominalCallables.close 1 source [42]))] := by
  apply NativeMatch.flat
  apply NativeMatchMany.next (.fresh rfl)
  apply NativeMatchMany.next
  · apply NativeMatch.existing rfl
    apply NativeEqual.callable
    simp [NominalCallables.same_close]
  · exact .nil

theorem repeated_variable_rejects_distinct_nominal_value :
    ¬ ∃ after, NativeMatch Nat (.flat [.bind 0, .bind 0])
      (.expression [.callable (NominalCallables.close 1 source []),
        .callable (NominalCallables.close 2 source [])]) [] after := by
  rintro ⟨after, matched⟩
  cases matched with
  | flat matched =>
      cases matched with
      | next first rest =>
          cases first with
          | fresh absent =>
              cases rest with
              | next second tail =>
                  cases second with
                  | fresh absent => simp [Native.lookup] at absent
                  | existing present equal =>
                      simp only [Native.lookup, ↓reduceIte, Option.some.injEq] at present
                      cases present
                      cases equal with
                      | callable equal => simp [NominalCallables.same_close] at equal
          | existing present equal => simp [Native.lookup] at present

def quotedLam : NativeTerm Nat := .expression [.symbol "Lam", .datum 0, .symbol "body"]
def quotedPartial : NativeTerm Nat :=
  .expression [.symbol "partial", .symbol "base", .expression [.datum 42]]

theorem quoted_lam_retains_flat_decomposition :
    NativeMatch Nat (.flat [.bind 0, .bind 1, .bind 2]) quotedLam []
      [(2, .symbol "body"), (1, .datum 0), (0, .symbol "Lam")] := by
  apply NativeMatch.flat
  apply NativeMatchMany.next (.fresh rfl)
  apply NativeMatchMany.next (.fresh (by decide))
  exact .next (.fresh (by decide)) .nil

theorem quoted_partial_retains_cons_decomposition :
    NativeMatch Nat (.cons (.literal (.symbol "partial")) (.bind 9)) quotedPartial []
      [(9, .expression [.symbol "base", .expression [.datum 42]])] :=
  .cons (.literal (.symbol "partial")) (.fresh rfl)

theorem reference_quoted_partial_retains_cons_decomposition :
    ReferenceMatch Nat (.cons (.literal (.symbol "partial")) (.bind 9))
      (.expression [.symbol "partial", .symbol "base", .expression [.datum 42]]) []
      [(9, .expression [.symbol "base", .expression [.datum 42]])] :=
  .cons (.literal (.symbol "partial")) (.fresh rfl)

theorem variable_identity_is_explicit_data :
    NativeMatch Nat (.literal (.variable 17)) (.variable 17) [] [] :=
  .literal (.variable 17)

theorem neutral_lam_field_leak_is_an_additional_match :
    exposedCodeFlatAccepts 3 captured = true ∧
    ¬ ∃ after, NativeMatch Nat (.flat [.bind 0, .bind 1, .bind 2]) (.callable captured) [] after :=
  exposed_code_forges_flat_match 1 source [42]

end Controls

end Mettapedia.Machines.IncrementalConformance.CallableMatchingBoundary
