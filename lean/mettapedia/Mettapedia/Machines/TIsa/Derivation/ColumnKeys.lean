import Mettapedia.Machines.TIsa.Derivation.OccurrenceIndex
import Mathlib.Data.List.MinMax
import Mathlib.Data.Rat.Encodable

/-!
# Column keys with an uncertain class

An index keeps, for one position of the stored atoms, a map from a
key to the occurrences whose element there has that key. A query
reads the occurrences offered under the key requested at that
position, then still compares each with the original matcher.

At a position, a stored element has a key, is *uncertain* (it may
meet values of many keys, as a stored variable does), or is a *miss*
(it can meet no requested key there). The candidates offered at a
chosen position are the occurrences whose element there has the
requested key or is uncertain. For every policy choosing the
position, the one with the shortest posting and the choice of none
included, these candidates form a `CandidateAccess`, so the matches
and their order are those of the full scan.

Sound filters combine by conjunction: the head restriction of an
occurrence index with a column, or two columns. The head of an atom
is its column zero, keyed like every other element, so a number in
head position needs nothing of its own.

Numbers compared by exact value across kinds share one key: an
integer is its value, a float equal to an integer is that integer,
any other float is its code. The same key is sound for the
comparison which keeps the kinds apart, because a key which is a
function of the value is sound wherever matching implies equality,
collisions included. A rational model of floats inhabits the
hypotheses. The controls show that keying floats by their codes
alone, or treating uncertain elements as misses, loses a match.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.ColumnKeys

universe u v w p k l

variable {T : Type u} {V : Type v} {B : Type w}

/-! ## Sound filters -/

/-- A filter on stored values, chosen from the store, the bindings and the pattern, is sound when
every successful comparison passes it. -/
def Sound (M : Matcher T V B) (keep : Store V → B → T → V → Bool) : Prop :=
  ∀ ⦃s : Store V⦄ ⦃bindings : B⦄ ⦃pattern : T⦄ ⦃value : V⦄ ⦃next : B⦄,
    M.extend bindings pattern value = some next → keep s bindings pattern value = true

variable {M : Matcher T V B}

/-- The occurrences which a sound filter keeps, in source order. -/
def filterAccess (keep : Store V → B → T → V → Bool) (sound : Sound M keep) :
    CandidateAccess M where
  read s bindings pattern :=
    s.occurrences.filter fun occurrence => keep s bindings pattern occurrence.2
  selects s bindings pattern := ⟨keep s bindings pattern, rfl, fun _ _ hit => sound hit⟩

namespace Sound

/-- Two sound filters combine by conjunction. -/
theorem and {first second : Store V → B → T → V → Bool} (sound₁ : Sound M first)
    (sound₂ : Sound M second) :
    Sound M fun s bindings pattern value =>
      first s bindings pattern value && second s bindings pattern value :=
  fun _ _ _ _ _ hit => by simp only [sound₁ hit, sound₂ hit, Bool.and_self]

/-- The head and argument restriction of an occurrence index is a sound filter. -/
theorem occurrenceIndex {Head : Type*} {Argument : Type*} [BEq Head] [BEq Argument]
    [LawfulBEq Head] [LawfulBEq Argument] (keys : IndexKeys M Head Argument) (width : ℕ) :
    Sound M fun _ bindings pattern value =>
      OccurrenceIndex.compatible keys width bindings pattern value :=
  fun _ _ _ _ _ hit => OccurrenceIndex.successful_is_compatible keys width hit

end Sound

/-! ## Keys at positions -/

/-- What a stored element says at one position: its key, that it is uncertain (it may meet values
of many keys), or a miss (it can meet no requested key). -/
inductive Projection (Key : Type k) where
  | key (own : Key)
  | uncertain
  | miss
  deriving DecidableEq, Repr

namespace Projection

variable {Key : Type k} {Key' : Type l}

/-- An element is offered to a requested key when its key is that key or it is uncertain. -/
def admits [DecidableEq Key] : Projection Key → Key → Bool
  | .key own, requested => decide (own = requested)
  | .uncertain, _ => true
  | .miss, _ => false

theorem admits_iff [DecidableEq Key] {projection : Projection Key} {requested : Key} :
    projection.admits requested = true ↔
      projection = .key requested ∨ projection = .uncertain := by
  cases projection <;> simp [admits]

/-- Re-encode the keys. -/
def map (encode : Key → Key') : Projection Key → Projection Key'
  | .key own => .key (encode own)
  | .uncertain => .uncertain
  | .miss => .miss

end Projection

/-- **Column keys** for a matcher. A stored value has a projection at every position, and the
bindings and a pattern may request a key at a position. A successful comparison meets, at each
position with a requested key, either that key or an uncertain element. -/
structure Keys (M : Matcher T V B) (Position : Type p) (Key : Type k) where
  project : V → Position → Projection Key
  request : B → T → Position → Option Key
  sound : ∀ {bindings pattern value next position requested},
    M.extend bindings pattern value = some next →
      request bindings pattern position = some requested →
      project value position = .key requested ∨ project value position = .uncertain

namespace Keys

variable {Position : Type p} {Key : Type k} {Key' : Type l} (keys : Keys M Position Key)

/-- **Keys that are functions of the value.** When the value at a position is itself a sound key,
that is, matching there implies equality of the values unless the stored element is uncertain, any
function of the value is a sound key. Distinct values may collide. -/
theorem sound_of_function (encode : Key → Key') {bindings : B} {pattern : T} {value : V}
    {next : B} {position : Position} {requested : Key'}
    (hit : M.extend bindings pattern value = some next)
    (wanted : (keys.request bindings pattern position).map encode = some requested) :
    (keys.project value position).map encode = .key requested ∨
      (keys.project value position).map encode = .uncertain := by
  obtain ⟨own, held, rfl⟩ := Option.map_eq_some_iff.mp wanted
  rcases keys.sound hit held with same | uncertain
  · exact .inl (by rw [same]; rfl)
  · exact .inr (by rw [uncertain]; rfl)

/-- The keys re-encoded by a function. -/
def map (encode : Key → Key') : Keys M Position Key' where
  project value position := (keys.project value position).map encode
  request bindings pattern position := (keys.request bindings pattern position).map encode
  sound hit wanted := keys.sound_of_function encode hit wanted

variable [DecidableEq Key]

/-- A value is offered at a position when no key is requested there, or its projection there
admits the requested key. -/
def offered (bindings : B) (pattern : T) (position : Position) (value : V) : Bool :=
  match keys.request bindings pattern position with
  | none => true
  | some requested => (keys.project value position).admits requested

theorem offered_of_extend {bindings : B} {pattern : T} {value : V} {next : B}
    (hit : M.extend bindings pattern value = some next) (position : Position) :
    keys.offered bindings pattern position value = true := by
  unfold offered
  cases wanted : keys.request bindings pattern position with
  | none => rfl
  | some requested => exact Projection.admits_iff.mpr (keys.sound hit wanted)

/-- Every column, read on its own, is a sound filter. -/
theorem sound_offered (position : Position) :
    Sound M fun _ bindings pattern value => keys.offered bindings pattern position value :=
  fun _ _ _ _ _ hit => keys.offered_of_extend hit position

/-- The test of a chosen position; without a choice every value is kept. -/
def chosen (choice : Option Position) (bindings : B) (pattern : T) (value : V) : Bool :=
  match choice with
  | none => true
  | some position => keys.offered bindings pattern position value

/-- Whatever position a policy chooses, from the store, the bindings and the pattern, the test of
that position is sound. -/
theorem sound_chosen (policy : Store V → B → T → Option Position) :
    Sound M fun s bindings pattern value =>
      keys.chosen (policy s bindings pattern) bindings pattern value := by
  intro s bindings pattern value next hit
  show keys.chosen (policy s bindings pattern) bindings pattern value = true
  unfold chosen
  cases policy s bindings pattern with
  | none => rfl
  | some position => exact keys.offered_of_extend hit position

/-- **The offered candidates** under a policy choosing at most one position. -/
def access (policy : Store V → B → T → Option Position) : CandidateAccess M :=
  filterAccess _ (keys.sound_chosen policy)

/-- The posting of a key at a position: the occurrences whose projection there admits it, in
source order. -/
def posting (s : Store V) (position : Position) (requested : Key) : List (ℕ × V) :=
  s.occurrences.filter fun occurrence => (keys.project occurrence.2 position).admits requested

theorem read_chosen {policy : Store V → B → T → Option Position} {s : Store V} {bindings : B}
    {pattern : T} {position : Position} {requested : Key}
    (chose : policy s bindings pattern = some position)
    (wanted : keys.request bindings pattern position = some requested) :
    (keys.access policy).read s bindings pattern = keys.posting s position requested := by
  change s.occurrences.filter (fun occurrence =>
    keys.chosen (policy s bindings pattern) bindings pattern occurrence.2) = _
  rw [chose]
  simp only [chosen, offered, wanted, posting]

theorem read_unchosen {policy : Store V → B → T → Option Position} {s : Store V} {bindings : B}
    {pattern : T} (chose : policy s bindings pattern = none) :
    (keys.access policy).read s bindings pattern = s.occurrences := by
  change s.occurrences.filter (fun occurrence =>
    keys.chosen (policy s bindings pattern) bindings pattern occurrence.2) = _
  rw [chose]
  simp only [chosen, List.filter_true]

/-- Every policy gives the firings of the full scan. -/
theorem firings_exact [DecidableEq V] (policy : Store V → B → T → Option Position)
    (program : List (Rule T)) (s : Store V) :
    firingsUsing M (keys.access policy) program s = firings M program s :=
  firingsUsing_exact M (keys.access policy) program s

/-! ### The shortest posting -/

/-- The columns with a requested key, each with the length of its posting. -/
def requestedPostings (columns : List Position) (s : Store V) (bindings : B) (pattern : T) :
    List (Position × ℕ) :=
  columns.filterMap fun position =>
    (keys.request bindings pattern position).map fun requested =>
      (position, (keys.posting s position requested).length)

/-- Choose the requested column with the shortest posting, the first such column on ties. -/
def shortest (columns : List Position) (s : Store V) (bindings : B) (pattern : T) :
    Option Position :=
  ((keys.requestedPostings columns s bindings pattern).argmin Prod.snd).map Prod.fst

theorem mem_requestedPostings {columns : List Position} {s : Store V} {bindings : B}
    {pattern : T} {position : Position} {length : ℕ} :
    (position, length) ∈ keys.requestedPostings columns s bindings pattern ↔
      position ∈ columns ∧ ∃ requested, keys.request bindings pattern position = some requested ∧
        (keys.posting s position requested).length = length := by
  simp only [requestedPostings, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨column, member, requested, wanted, rfl, rfl⟩
    exact ⟨member, requested, wanted, rfl⟩
  · rintro ⟨member, requested, wanted, rfl⟩
    exact ⟨position, member, requested, wanted, rfl, rfl⟩

theorem shortest_requested {columns : List Position} {s : Store V} {bindings : B} {pattern : T}
    {position : Position} (chose : keys.shortest columns s bindings pattern = some position) :
    position ∈ columns ∧ (keys.request bindings pattern position).isSome := by
  obtain ⟨⟨column, length⟩, least, rfl⟩ := Option.map_eq_some_iff.mp chose
  obtain ⟨member, requested, wanted, -⟩ := keys.mem_requestedPostings.mp (List.argmin_mem least)
  exact ⟨member, by rw [wanted]; rfl⟩

/-- The shortest policy chooses a posting no longer than that of any requested column. -/
theorem shortest_minimal {columns : List Position} {s : Store V} {bindings : B} {pattern : T}
    {position column : Position} {requested other : Key}
    (chose : keys.shortest columns s bindings pattern = some position)
    (wanted : keys.request bindings pattern position = some requested)
    (member : column ∈ columns) (otherWanted : keys.request bindings pattern column = some other) :
    (keys.posting s position requested).length ≤ (keys.posting s column other).length := by
  obtain ⟨⟨chosenColumn, length⟩, least, rfl⟩ := Option.map_eq_some_iff.mp chose
  obtain ⟨-, same, sameWanted, rfl⟩ := keys.mem_requestedPostings.mp (List.argmin_mem least)
  rw [wanted] at sameWanted
  cases sameWanted
  exact List.le_of_mem_argmin (f := Prod.snd)
    (keys.mem_requestedPostings.mpr ⟨member, other, otherWanted, rfl⟩) least

theorem shortest_eq_none {columns : List Position} {s : Store V} {bindings : B} {pattern : T} :
    keys.shortest columns s bindings pattern = none ↔
      ∀ column ∈ columns, keys.request bindings pattern column = none := by
  simp only [shortest, Option.map_eq_none_iff, List.argmin_eq_none, requestedPostings,
    List.filterMap_eq_nil_iff, Option.map_eq_none_iff]

theorem shortest_firings_exact [DecidableEq V] (columns : List Position)
    (program : List (Rule T)) (s : Store V) :
    firingsUsing M (keys.access (keys.shortest columns)) program s = firings M program s :=
  keys.firings_exact _ program s

theorem none_firings_exact [DecidableEq V] (program : List (Rule T)) (s : Store V) :
    firingsUsing M (keys.access fun _ _ _ => none) program s = firings M program s :=
  keys.firings_exact _ program s

/-! ### Composition -/

/-- Two columns read together: the occurrences offered at both. -/
def bothColumns (first second : Position) : CandidateAccess M :=
  filterAccess _ ((keys.sound_offered first).and (keys.sound_offered second))

/-- The head and argument restriction of an occurrence index, together with a column chosen by any
policy. -/
def withIndex {Head : Type*} {Argument : Type*} [BEq Head] [BEq Argument] [LawfulBEq Head]
    [LawfulBEq Argument] (index : IndexKeys M Head Argument) (width : ℕ)
    (policy : Store V → B → T → Option Position) : CandidateAccess M :=
  filterAccess _ ((Sound.occurrenceIndex index width).and (keys.sound_chosen policy))

theorem bothColumns_firings_exact [DecidableEq V] (first second : Position)
    (program : List (Rule T)) (s : Store V) :
    firingsUsing M (keys.bothColumns first second) program s = firings M program s :=
  firingsUsing_exact M _ program s

theorem withIndex_firings_exact [DecidableEq V] {Head : Type*} {Argument : Type*} [BEq Head]
    [BEq Argument] [LawfulBEq Head] [LawfulBEq Argument] (index : IndexKeys M Head Argument)
    (width : ℕ) (policy : Store V → B → T → Option Position) (program : List (Rule T))
    (s : Store V) :
    firingsUsing M (keys.withIndex index width policy) program s = firings M program s :=
  firingsUsing_exact M _ program s

end Keys

/-! ## Flat atoms -/

section Flat

variable {G : Type*} {K : Type k}

/-- An element of a stored atom: a ground element, or a variable of the stored atom. -/
inductive Stored (G : Type*) where
  | ground (element : G)
  | var
  deriving DecidableEq, Repr

/-- An element of a pattern: a ground element, or a pattern variable. -/
inductive Pattern (G : Type*) where
  | ground (element : G)
  | var (name : ℕ)
  deriving DecidableEq, Repr

/-- Bindings of pattern variables to stored elements, newest first. -/
abbrev Bindings (G : Type*) := List (ℕ × Stored G)

/-- Two stored elements are compatible when both are ground and equal, or either is a variable. -/
def Stored.compatible (equal : G → G → Bool) : Stored G → Stored G → Bool
  | .ground a, .ground b => equal a b
  | _, _ => true

/-- One pattern element against one stored element. A ground element must be compatible with the
stored one; a pattern variable binds the first element it meets and must be compatible with it at
every later meeting. -/
def meet (equal : G → G → Bool) (bindings : Bindings G) :
    Pattern G → Stored G → Option (Bindings G)
  | .ground a, stored => if (Stored.ground a).compatible equal stored then some bindings else none
  | .var x, stored =>
    match bindings.lookup x with
    | none => some ((x, stored) :: bindings)
    | some bound => if bound.compatible equal stored then some bindings else none

/-- A flat pattern against a flat stored atom of the same length, position by position. -/
def extendAll (equal : G → G → Bool) :
    Bindings G → List (Pattern G) → List (Stored G) → Option (Bindings G)
  | bindings, [], [] => some bindings
  | bindings, element :: pattern, stored :: atom =>
    (meet equal bindings element stored).bind fun next => extendAll equal next pattern atom
  | _, _, _ => none

/-- A flat pattern read under bindings as a stored atom. -/
def instantiateAll (bindings : Bindings G) : List (Pattern G) → Option (List (Stored G))
  | [] => some []
  | .ground a :: pattern => (instantiateAll bindings pattern).map (.ground a :: ·)
  | .var x :: pattern =>
    (bindings.lookup x).bind fun bound => (instantiateAll bindings pattern).map (bound :: ·)

/-- The flat matcher of an equality of ground elements. -/
def flat (equal : G → G → Bool) : Matcher (List (Pattern G)) (List (Stored G)) (Bindings G) where
  empty := []
  extend := extendAll equal
  instantiate := instantiateAll

/-- A stored element's key: a ground element's key, or uncertain for a variable. -/
def Stored.project (key : G → K) : Stored G → Projection K
  | .ground a => .key (key a)
  | .var => .uncertain

/-- The key a pattern element requests: its own key when ground, the key of the ground element its
variable is bound to, and none when the variable is unbound or bound to a stored variable. -/
def Pattern.request (key : G → K) (bindings : Bindings G) : Pattern G → Option K
  | .ground a => some (key a)
  | .var x =>
    match bindings.lookup x with
    | some (.ground a) => some (key a)
    | _ => none

/-- The projection of a flat atom at a position; a miss beyond its length. -/
def projectAt (key : G → K) (atom : List (Stored G)) (position : ℕ) : Projection K :=
  ((atom[position]?).map (Stored.project key)).getD .miss

/-- The key a flat pattern requests at a position under bindings. -/
def requestAt (key : G → K) (bindings : Bindings G) (pattern : List (Pattern G)) (position : ℕ) :
    Option K :=
  (pattern[position]?).bind (Pattern.request key bindings)

theorem meet_lookup {equal : G → G → Bool} {bindings next : Bindings G} {element : Pattern G}
    {stored : Stored G} (hit : meet equal bindings element stored = some next) {x : ℕ}
    {bound : Stored G} (held : bindings.lookup x = some bound) : next.lookup x = some bound := by
  cases element with
  | ground a =>
    simp only [meet] at hit
    split at hit
    · cases hit; exact held
    · cases hit
  | var y =>
    simp only [meet] at hit
    cases fresh : bindings.lookup y with
    | none =>
      rw [fresh] at hit
      cases hit
      have apart : x ≠ y := by
        rintro rfl
        rw [held] at fresh
        cases fresh
      have differ : (x == y) = false := by simpa using apart
      simp [List.lookup_cons, differ, held]
    | some earlier =>
      rw [fresh] at hit
      simp only at hit
      split at hit
      · cases hit; exact held
      · cases hit

theorem requestAt_mono {key : G → K} {bindings next : Bindings G}
    (keeps : ∀ {x : ℕ} {bound : Stored G},
      bindings.lookup x = some bound → next.lookup x = some bound)
    {pattern : List (Pattern G)} {position : ℕ} {requested : K}
    (wanted : requestAt key bindings pattern position = some requested) :
    requestAt key next pattern position = some requested := by
  unfold requestAt at wanted ⊢
  cases element : pattern[position]? with
  | none => rw [element] at wanted; cases wanted
  | some element' =>
    rw [element] at wanted
    cases element' with
    | ground a => exact wanted
    | var x =>
      simp only [Option.bind_some, Pattern.request] at wanted ⊢
      cases bound : bindings.lookup x with
      | none => rw [bound] at wanted; cases wanted
      | some stored =>
        rw [bound] at wanted
        rw [keeps bound]
        exact wanted

variable {equal : G → G → Bool} {key : G → K}

theorem meet_sound (agrees : ∀ {a b : G}, equal a b = true → key a = key b)
    {bindings next : Bindings G} {element : Pattern G} {stored : Stored G} {requested : K}
    (hit : meet equal bindings element stored = some next)
    (wanted : element.request key bindings = some requested) :
    stored.project key = .key requested ∨ stored.project key = .uncertain := by
  have ground : ∀ a, key a = requested → (Stored.ground a).compatible equal stored = true →
      stored.project key = .key requested ∨ stored.project key = .uncertain := by
    intro a keyed compatible
    cases stored with
    | ground b =>
      have equalElements : equal a b = true := compatible
      exact .inl (by rw [Stored.project, ← keyed, agrees equalElements])
    | var => exact .inr rfl
  cases element with
  | ground a =>
    simp only [Pattern.request, Option.some.injEq] at wanted
    simp only [meet] at hit
    split at hit
    · exact ground a wanted (by assumption)
    · cases hit
  | var x =>
    simp only [Pattern.request] at wanted
    cases bound : bindings.lookup x with
    | none => rw [bound] at wanted; cases wanted
    | some earlier =>
      rw [bound] at wanted
      cases earlier with
      | var => cases wanted
      | ground a =>
        simp only [Option.some.injEq] at wanted
        simp only [meet, bound] at hit
        split at hit
        · exact ground a wanted (by assumption)
        · cases hit

theorem extendAll_sound (agrees : ∀ {a b : G}, equal a b = true → key a = key b) :
    ∀ {bindings : Bindings G} {pattern : List (Pattern G)} {atom : List (Stored G)}
      {next : Bindings G} {position : ℕ} {requested : K},
      extendAll equal bindings pattern atom = some next →
      requestAt key bindings pattern position = some requested →
      projectAt key atom position = .key requested ∨ projectAt key atom position = .uncertain
  | _, [], [], _, _, _, _, wanted => by simp [requestAt] at wanted
  | _, [], _ :: _, _, _, _, hit, _ => by simp [extendAll] at hit
  | _, _ :: _, [], _, _, _, hit, _ => by simp [extendAll] at hit
  | bindings, element :: pattern, stored :: atom, next, position, requested, hit, wanted => by
    simp only [extendAll, Option.bind_eq_some_iff] at hit
    obtain ⟨between, first, rest⟩ := hit
    cases position with
    | zero =>
      simp only [requestAt, List.getElem?_cons_zero, Option.bind_some] at wanted
      simp only [projectAt, List.getElem?_cons_zero, Option.map_some, Option.getD_some]
      exact meet_sound (equal := equal) (key := key) agrees first wanted
    | succ position =>
      simp only [requestAt, List.getElem?_cons_succ] at wanted
      simp only [projectAt, List.getElem?_cons_succ]
      exact extendAll_sound agrees rest
        (requestAt_mono (fun held => meet_lookup first held) wanted)

/-- **Column keys of flat atoms.** Every position, the head at position zero included, is keyed by
the key of its element, sound whenever equal ground elements have equal keys. -/
def flatKeys (equal : G → G → Bool) (key : G → K)
    (agrees : ∀ {a b : G}, equal a b = true → key a = key b) : Keys (flat equal) ℕ K where
  project := projectAt key
  request := requestAt key
  sound hit wanted := extendAll_sound (equal := equal) (key := key) agrees hit wanted

theorem extendAll_length :
    ∀ {bindings : Bindings G} {pattern : List (Pattern G)} {atom : List (Stored G)}
      {next : Bindings G}, extendAll equal bindings pattern atom = some next →
      pattern.length = atom.length
  | _, [], [], _, _ => rfl
  | _, [], _ :: _, _, hit => by simp [extendAll] at hit
  | _, _ :: _, [], _, hit => by simp [extendAll] at hit
  | _, _ :: _, _ :: _, _, hit => by
    simp only [extendAll, Option.bind_eq_some_iff] at hit
    obtain ⟨_, _, rest⟩ := hit
    simp [extendAll_length rest]

/-- The arity of a flat atom as the head of an occurrence index: a pattern meets only atoms of its
own length. No argument is keyed. -/
def arityKeys (equal : G → G → Bool) : IndexKeys (flat equal) ℕ Unit where
  head atom := atom.length
  argument _ _ := none
  needHead _ pattern := some pattern.length
  needArgument _ _ := none
  head_sound hit required := by
    cases required
    exact (extendAll_length hit).symm
  argument_sound _ required := by cases required

end Flat

/-! ## Numbers -/

universe f

/-- A number: an integer or a float. -/
inductive Number (F : Type f) where
  | integer (value : ℤ)
  | float (value : F)
  deriving DecidableEq, Repr

/-- **A number domain.** `feq` is the equality of floats, `exactInt` gives the integer a float
equals if there is one, and `bits` is a code of a float. Equal floats equal the same integer, and
equal floats which equal no integer have the same code. -/
structure NumberDomain (F : Type f) where
  feq : F → F → Bool
  exactInt : F → Option ℤ
  bits : F → ℕ
  exactInt_congr : ∀ {x y : F}, feq x y = true → exactInt x = exactInt y
  bits_congr : ∀ {x y : F}, feq x y = true → exactInt x = none → bits x = bits y

namespace NumberDomain

variable {F : Type f} (D : NumberDomain F)

/-- Equality of numbers by exact value: integers by value, floats by `feq`, and an integer equals
a float exactly when the float equals that integer. -/
def sameValue : Number F → Number F → Bool
  | .integer i, .integer j => decide (i = j)
  | .float x, .float y => D.feq x y
  | .integer i, .float y => decide (D.exactInt y = some i)
  | .float x, .integer j => decide (D.exactInt x = some j)

/-- **The key of a number.** An integer is its value, a float equal to an integer is that integer,
and any other float is its code. -/
def key : Number F → ℤ ⊕ ℕ
  | .integer i => .inl i
  | .float x =>
    match D.exactInt x with
    | some i => .inl i
    | none => .inr (D.bits x)

/-- The key is sound for equality by exact value. -/
theorem key_of_sameValue {a b : Number F} (same : D.sameValue a b = true) : D.key a = D.key b := by
  cases a with
  | integer i =>
    cases b with
    | integer j =>
      simp only [sameValue, decide_eq_true_eq] at same
      rw [same]
    | float y =>
      simp only [sameValue, decide_eq_true_eq] at same
      simp only [key, same]
  | float x =>
    cases b with
    | integer j =>
      simp only [sameValue, decide_eq_true_eq] at same
      simp only [key, same]
    | float y =>
      simp only [sameValue] at same
      have sameInt := D.exactInt_congr same
      simp only [key, ← sameInt]
      cases integral : D.exactInt x with
      | some i => rfl
      | none => simp only [D.bits_congr same integral]

/-- The key of every float by its code alone, integral or not. -/
def codeKey : Number F → ℤ ⊕ ℕ
  | .integer i => .inl i
  | .float x => .inr (D.bits x)

end NumberDomain

/-! ### Ground elements with symbols and numbers -/

section Ground

variable {S : Type*} {F : Type f} {H : Type k}

/-- A ground element of a flat atom: a symbol or a number. -/
inductive Ground (S : Type*) (F : Type f) where
  | symbol (name : S)
  | number (value : Number F)
  deriving DecidableEq, Repr

variable [DecidableEq S] (D : NumberDomain F)

/-- Equality of ground elements which relates numbers of different kinds by exact value. -/
def Ground.sameValue : Ground S F → Ground S F → Bool
  | .symbol a, .symbol b => decide (a = b)
  | .number m, .number n => D.sameValue m n
  | _, _ => false

omit [DecidableEq S] in
/-- The key of a ground element: a code of a symbol's name, or the key of a number. -/
def Ground.key (code : S → H) : Ground S F → H ⊕ (ℤ ⊕ ℕ)
  | .symbol a => .inl (code a)
  | .number n => .inr (D.key n)

theorem Ground.key_of_sameValue (code : S → H) {a b : Ground S F}
    (same : Ground.sameValue D a b = true) : Ground.key D code a = Ground.key D code b := by
  cases a with
  | symbol x =>
    cases b with
    | symbol y =>
      simp only [Ground.sameValue, decide_eq_true_eq] at same
      rw [same]
    | number _ => simp [Ground.sameValue] at same
  | number m =>
    cases b with
    | symbol _ => simp [Ground.sameValue] at same
    | number n =>
      simp only [Ground.key, D.key_of_sameValue same]

/-- Column keys of flat atoms compared by exact value across number kinds. -/
def valueKeys (code : S → H) : Keys (flat (Ground.sameValue (S := S) D)) ℕ (H ⊕ (ℤ ⊕ ℕ)) :=
  flatKeys (Ground.sameValue D) (Ground.key D code) (Ground.key_of_sameValue D code)

/-- Identity of elements, the equality which keeps number kinds apart. -/
def identical {G : Type*} [DecidableEq G] (a b : G) : Bool := decide (a = b)

/-- Under identity, matching at a position implies equality, so the element itself is a sound key
there. -/
def identityValueKeys {G : Type*} [DecidableEq G] : Keys (flat (identical (G := G))) ℕ G :=
  flatKeys identical id fun same => of_decide_eq_true same

/-- Column keys of flat atoms compared by identity: the same number key, as a function of the
element. -/
def identityKeys [DecidableEq F] (code : S → H) :
    Keys (flat (identical (G := Ground S F))) ℕ (H ⊕ (ℤ ⊕ ℕ)) :=
  identityValueKeys.map (Ground.key D code)

/-- **One key serves both comparisons.** The projections and requests of the two column keys are
the same functions. -/
theorem identityKeys_eq_valueKeys [DecidableEq F] (code : S → H) :
    (identityKeys D code).project = (valueKeys D code).project ∧
      (identityKeys D code).request = (valueKeys D code).request := by
  constructor
  · funext atom position
    change (projectAt id atom position).map (Ground.key D code) =
      projectAt (Ground.key D code) atom position
    unfold projectAt
    cases atom[position]? with
    | none => rfl
    | some stored => cases stored <;> rfl
  · funext bindings pattern position
    change (requestAt id bindings pattern position).map (Ground.key D code) =
      requestAt (Ground.key D code) bindings pattern position
    unfold requestAt
    cases pattern[position]? with
    | none => rfl
    | some element =>
      cases element with
      | ground a => rfl
      | var x =>
        simp only [Option.bind_some, Pattern.request]
        cases bindings.lookup x with
        | none => rfl
        | some bound => cases bound <;> rfl

/-- **A number head is column zero.** A flat atom whose head is a number projects that number's
key at position zero, and a pattern with a number head requests it there, like any other
position. -/
theorem number_head_is_column_zero (code : S → H) (n : Number F) (atom : List (Stored (Ground S F)))
    (pattern : List (Pattern (Ground S F))) (bindings : Bindings (Ground S F)) :
    (valueKeys D code).project (.ground (.number n) :: atom) 0 = .key (.inr (D.key n)) ∧
      (valueKeys D code).request bindings (.ground (.number n) :: pattern) 0 =
        some (.inr (D.key n)) :=
  ⟨rfl, rfl⟩

end Ground

/-! ## A rational model of floats -/

/-- Floats valued in the rationals, with a negative zero, two infinities and a value which is not a
number. The binary64 values form a subset. -/
inductive RationalFloat where
  | finite (value : ℚ)
  | negativeZero
  | positiveInfinity
  | negativeInfinity
  | notANumber
  deriving DecidableEq, Repr

namespace RationalFloat

/-- Equality of floats: finite values by value, the two zeros equal, each infinity equal to itself,
and the value which is not a number equal to nothing. -/
def feq : RationalFloat → RationalFloat → Bool
  | .finite a, .finite b => decide (a = b)
  | .finite a, .negativeZero => decide (a = 0)
  | .negativeZero, .finite b => decide (b = 0)
  | .negativeZero, .negativeZero => true
  | .positiveInfinity, .positiveInfinity => true
  | .negativeInfinity, .negativeInfinity => true
  | _, _ => false

/-- The integer a float equals: the value of an integral finite float, and zero for the negative
zero. -/
def exactInt : RationalFloat → Option ℤ
  | .finite a => if a.den = 1 then some a.num else none
  | .negativeZero => some 0
  | _ => none

/-- A code of a float, distinct for distinct floats. -/
def bits : RationalFloat → ℕ
  | .finite a => 4 * Encodable.encode a + 4
  | .negativeZero => 0
  | .positiveInfinity => 1
  | .negativeInfinity => 2
  | .notANumber => 3

theorem bits_injective : Function.Injective bits := by
  intro x y same
  cases x <;> cases y <;> simp only [bits] at same <;> try omega
  · rename_i a b
    have codes : Encodable.encode a = Encodable.encode b := by omega
    rw [Encodable.encode_injective codes]
  all_goals rfl

theorem exactInt_congr {x y : RationalFloat} (same : feq x y = true) : exactInt x = exactInt y := by
  cases x <;> cases y <;> simp_all [feq, exactInt]

theorem bits_congr {x y : RationalFloat} (same : feq x y = true) (fractional : exactInt x = none) :
    bits x = bits y := by
  cases x <;> cases y <;> simp_all [feq, exactInt]

/-- The rational model as a number domain. -/
def domain : NumberDomain RationalFloat where
  feq := feq
  exactInt := exactInt
  bits := bits
  exactInt_congr := exactInt_congr
  bits_congr := bits_congr

/-- An integer equals the float of its value. -/
theorem integer_equals_its_float : domain.sameValue (.integer 9) (.float (.finite 9)) = true := by
  decide +kernel

/-- Exact comparison: the integer 2^53 + 1 does not equal the float 2^53. -/
theorem beyond_the_float :
    domain.sameValue (.integer (2 ^ 53 + 1)) (.float (.finite (2 ^ 53))) = false ∧
      domain.sameValue (.integer (2 ^ 53)) (.float (.finite (2 ^ 53))) = true := by
  decide +kernel

/-- The two zeros are equal to each other and to the integer zero, and share its key, although
their codes differ. -/
theorem zeros_share_the_key :
    domain.sameValue (.float .negativeZero) (.float (.finite 0)) = true ∧
      domain.sameValue (.integer 0) (.float .negativeZero) = true ∧
      domain.key (.float .negativeZero) = .inl 0 ∧ domain.key (.float (.finite 0)) = .inl 0 ∧
      bits .negativeZero ≠ bits (.finite 0) := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, by decide +kernel, ?_⟩
  simp only [bits]
  omega

/-- Codes alone do not respect float equality: the law on codes holds only for floats which equal
no integer. -/
theorem codes_separate_equal_floats : ¬∀ x y, feq x y = true → bits x = bits y :=
  fun law => zeros_share_the_key.2.2.2.2 (law .negativeZero (.finite 0) (by decide +kernel))

/-- The value which is not a number equals no number, itself included. -/
theorem notANumber_equals_nothing (n : Number RationalFloat) :
    domain.sameValue (.float .notANumber) n = false ∧
      domain.sameValue n (.float .notANumber) = false := by
  cases n with
  | integer i => exact ⟨rfl, rfl⟩
  | float y => cases y <;> exact ⟨rfl, rfl⟩

/-- Identity keeps the kinds apart and the two zeros apart. -/
theorem identity_keeps_kinds_apart :
    identical (Number.integer 9 : Number RationalFloat) (.float (.finite 9)) = false ∧
      identical (Number.float .negativeZero : Number RationalFloat) (.float (.finite 0)) =
        false := by
  decide +kernel

/-- Keying floats by their codes alone is not sound for equality by exact value. -/
theorem codeKey_unsound :
    domain.sameValue (.integer 9) (.float (.finite 9)) = true ∧
      domain.codeKey (.integer 9) ≠ domain.codeKey (.float (.finite 9)) :=
  ⟨integer_equals_its_float, by simp [NumberDomain.codeKey]⟩

end RationalFloat

/-! ## Controls on flat atoms -/

section Examples

open RationalFloat

private abbrev Element := Ground String RationalFloat

private abbrev Atom := List (Stored Element)

private def nameCode (name : String) : ℕ :=
  name.toList.foldl (fun code c => 31 * code + c.toNat) 7

private def sym (name : String) : Stored Element := .ground (.symbol name)

private def int (i : ℤ) : Stored Element := .ground (.number (.integer i))

private def flo (q : ℚ) : Stored Element := .ground (.number (.float (.finite q)))

private def psym (name : String) : Pattern Element := .ground (.symbol name)

private def pint (i : ℤ) : Pattern Element := .ground (.number (.integer i))

private abbrev matcher : Matcher (List (Pattern Element)) Atom (Bindings Element) :=
  flat (Ground.sameValue domain)

private abbrev keys : Keys matcher ℕ (ℕ ⊕ (ℤ ⊕ ℕ)) := valueKeys domain nameCode

private def start : Match Atom (Bindings Element) := Match.start matcher

private def reading (pattern : List (Pattern Element)) : Rule (List (Pattern Element)) :=
  ⟨PUnit.unit, ⟨[], [pattern], [], [], []⟩, []⟩

/-! ### Keying floats by their codes alone -/

private def nines : Store Atom := ⟨[(0, [sym "t", int 9]), (1, [sym "t", flo 9])], 2⟩

private def askNine : List (Pattern Element) := [psym "t", pint 9]

private def codeProjection (atom : Atom) : Projection (ℕ ⊕ (ℤ ⊕ ℕ)) :=
  projectAt (fun a => match a with
    | .symbol name => .inl (nameCode name)
    | .number n => .inr (domain.codeKey n)) atom 1

/-- The read of column one under keys which code every float by its bits. -/
private def codeRead : List (ℕ × Atom) :=
  nines.occurrences.filter fun occurrence =>
    (codeProjection occurrence.2).admits (.inr (domain.codeKey (.integer 9)))

/-- The full scan finds both `9` and `9.0`; the read under codes alone finds one. -/
theorem code_read_drops_an_answer :
    (nines.occurrences.filterMap (attempt matcher .read askNine start)).length = 2 ∧
      (codeRead.filterMap (attempt matcher .read askNine start)).length = 1 := by
  decide +kernel

/-- No candidate access reads what codes alone offer. -/
theorem no_access_reads_by_codes_alone :
    ¬∃ wrong : CandidateAccess matcher, wrong.read nines [] askNine = codeRead := by
  rintro ⟨wrong, codeOnly⟩
  have equal := wrong.exact nines .read askNine start
  change (wrong.read nines [] askNine).filterMap _ = _ at equal
  rw [codeOnly] at equal
  have counted := congrArg List.length equal
  rw [code_read_drops_an_answer.1, code_read_drops_an_answer.2] at counted
  omega

/-- The exact key offers both. -/
theorem exact_key_offers_both : (keys.posting nines 1 (.inr (.inl 9))).map Prod.fst = [0, 1] := by
  decide +kernel

/-! ### Treating uncertain elements as misses -/

private def withVariable : Store Atom :=
  ⟨[(0, [sym "t", int 9]), (1, [sym "t", .var]), (2, [sym "t", int 10])], 3⟩

/-- Admission which treats an uncertain element as a miss. -/
private def admitsKeyOnly (projection : Projection (ℕ ⊕ (ℤ ⊕ ℕ))) (requested : ℕ ⊕ (ℤ ⊕ ℕ)) :
    Bool :=
  match projection with
  | .key own => decide (own = requested)
  | _ => false

private def missRead : List (ℕ × Atom) :=
  withVariable.occurrences.filter fun occurrence =>
    admitsKeyOnly (keys.project occurrence.2 1) (.inr (.inl 9))

/-- The stored variable matches `9`; the read which treats it as a miss drops it. -/
theorem miss_read_drops_the_variable :
    (withVariable.occurrences.filterMap (attempt matcher .read askNine start)).map
        (fun m => m.read) = [[0], [1]] ∧
      (missRead.filterMap (attempt matcher .read askNine start)).map (fun m => m.read) = [[0]] := by
  decide +kernel

theorem no_access_treats_uncertain_as_miss :
    ¬∃ wrong : CandidateAccess matcher, wrong.read withVariable [] askNine = missRead := by
  rintro ⟨wrong, missing⟩
  have equal := wrong.exact withVariable .read askNine start
  change (wrong.read withVariable [] askNine).filterMap _ = _ at equal
  rw [missing] at equal
  have counted := congrArg (List.map fun m => m.read) equal
  rw [miss_read_drops_the_variable.1, miss_read_drops_the_variable.2] at counted
  simp at counted

/-! ### A number column at position zero -/

private def numberHeads : Store Atom :=
  ⟨[(0, [int 9, sym "a"]), (1, [flo 9, sym "b"]), (2, [int 10, sym "c"]), (3, [.var, sym "c"]),
    (4, [sym "f", sym "e"]), (5, [flo (1 / 2), sym "a"]), (6, [int 9]), (7, [.var, sym "a"])], 8⟩

private def headNine : List (Pattern Element) := [pint 9, .var 0]

private def headNineA : List (Pattern Element) := [pint 9, psym "a"]

/-- Column zero offers the occurrences with head `9`, `9.0` or a stored variable, and the
indexed rule has exactly the firings of the full scan. -/
theorem number_column_selects_exactly :
    ((keys.access fun _ _ _ => some 0).read numberHeads [] headNine).map Prod.fst =
        [0, 1, 3, 6, 7] ∧
      (firingsUsing matcher (keys.access fun _ _ _ => some 0) [reading headNine] numberHeads).map
        (fun firing => firing.2.read) = [[0], [1], [3], [7]] := by
  rw [keys.firings_exact]
  decide +kernel

/-- With both columns requested, the shortest posting is column one; reading both columns offers
their common occurrences; every choice gives the firings of the full scan. -/
theorem shortest_and_both_columns :
    keys.shortest [0, 1] numberHeads [] headNineA = some 1 ∧
      ((keys.access (keys.shortest [0, 1])).read numberHeads [] headNineA).map Prod.fst =
        [0, 5, 7] ∧
      ((keys.bothColumns 0 1).read numberHeads [] headNineA).map Prod.fst = [0, 7] ∧
      (firingsUsing matcher (keys.access (keys.shortest [0, 1])) [reading headNineA]
          numberHeads).map (fun firing => firing.2.read) = [[0], [7]] ∧
      (firingsUsing matcher (keys.bothColumns 0 1) [reading headNineA] numberHeads).map
          (fun firing => firing.2.read) = [[0], [7]] := by
  rw [keys.shortest_firings_exact, keys.bothColumns_firings_exact]
  decide +kernel

/-- The arity restriction of an occurrence index together with column zero. -/
theorem arity_with_column_zero :
    ((keys.withIndex (arityKeys _) 0 fun _ _ _ => some 0).read numberHeads [] headNine).map
        Prod.fst = [0, 1, 3, 7] ∧
      (firingsUsing matcher (keys.withIndex (arityKeys _) 0 fun _ _ _ => some 0)
          [reading headNine] numberHeads).map (fun firing => firing.2.read) =
        [[0], [1], [3], [7]] := by
  rw [keys.withIndex_firings_exact]
  decide +kernel

end Examples

end Mettapedia.Machines.TIsa.Derivation.ColumnKeys
