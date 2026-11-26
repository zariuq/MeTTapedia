import Mettapedia.Machines.TIsa.Derivation.CandidateSearch
import Std.Data.HashMap.Lemmas

/-!
# Ordered postings for head and argument keys

A bucket contains occurrences, including distinct identities carrying
the same value. An available argument key refines the head bucket.
Unknown keys, or arguments for which no index was built, leave the
broader search intact. The comparison after lookup is still the
original matcher.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation

universe u v w h k

namespace OccurrencePostings

variable {A : Type v} {Key : Type k} [BEq Key] [Hashable Key]

def bucket (groups : Std.HashMap Key (List A)) (selected : Key) : List A :=
  groups[selected]?.getD []

def group (key : A → Key) : List A → Std.HashMap Key (List A)
  | [] => ∅
  | a :: rest =>
    let groups := group key rest
    groups.insert (key a) (a :: bucket groups (key a))

theorem bucket_group [LawfulBEq Key] (key : A → Key) (items : List A) (selected : Key) :
    bucket (group key items) selected = items.filter (fun a => key a == selected) := by
  induction items with
  | nil => simp [group, bucket]
  | cons a tail ih =>
    change ((group key tail).insert (key a) (a :: bucket (group key tail) (key a)))[selected]?.getD [] = _
    rw [Std.HashMap.getElem?_insert, List.filter_cons]
    by_cases same : key a == selected
    · simp only [if_pos same, Option.getD_some]
      rw [eq_of_beq same, ih]
    · simp only [if_neg same]
      exact ih

end OccurrencePostings

variable {T : Type u} {V : Type v} {B : Type w} {Head : Type h} {Argument : Type k}
  {M : Matcher T V B}

structure IndexKeys (M : Matcher T V B) (Head : Type h) (Argument : Type k) where
  head : V → Head
  argument : V → ℕ → Option Argument
  needHead : B → T → Option Head
  needArgument : B → T → Option (ℕ × Argument)
  head_sound : ∀ {bindings pattern value next headKey},
    M.extend bindings pattern value = some next → needHead bindings pattern = some headKey →
    head value = headKey
  argument_sound : ∀ {bindings pattern value next position key},
    M.extend bindings pattern value = some next → needArgument bindings pattern = some (position, key) →
    argument value position = some key

/-- The heads and each materialized argument coordinate are built once
for a snapshot; queries may consult any bucket without scanning it into
existence. -/
structure OccurrenceIndex (V : Type v) (Head : Type h) (Argument : Type k)
    [BEq Head] [Hashable Head] [BEq Argument] [Hashable Argument] where
  all : List (ℕ × V)
  heads : Std.HashMap Head (List (ℕ × V))
  arguments : List (Std.HashMap (Head × Option Argument) (List (ℕ × V)))

namespace OccurrenceIndex

open OccurrencePostings

variable [BEq Head] [Hashable Head] [BEq Argument] [Hashable Argument]

def build (keys : IndexKeys M Head Argument) (width : ℕ) (s : Store V) :
    OccurrenceIndex V Head Argument where
  all := s.occurrences
  heads := group (keys.head ∘ Prod.snd) s.occurrences
  arguments := (List.range width).map fun i =>
    group (fun a => (keys.head a.2, keys.argument a.2 i)) s.occurrences

def query (keys : IndexKeys M Head Argument) (index : OccurrenceIndex V Head Argument)
    (bindings : B) (pattern : T) : List (ℕ × V) :=
  match keys.needHead bindings pattern with
  | none => index.all
  | some h =>
    let broad := bucket index.heads h
    match keys.needArgument bindings pattern with
    | none => broad
    | some (i, a) =>
      match index.arguments[i]? with
      | none => broad
      | some indexed => bucket indexed (h, some a)

def compatible (keys : IndexKeys M Head Argument) (width : ℕ)
    (bindings : B) (pattern : T) (value : V) : Bool :=
  match keys.needHead bindings pattern with
  | none => true
  | some h =>
    match keys.needArgument bindings pattern with
    | none => keys.head value == h
    | some (i, a) =>
      if i < width then (keys.head value, keys.argument value i) == (h, some a)
      else keys.head value == h

variable [LawfulBEq Head] [LawfulBEq Argument]

theorem query_eq_filter (keys : IndexKeys M Head Argument) (width : ℕ) (s : Store V)
    (bindings : B) (pattern : T) :
    query keys (build keys width s) bindings pattern =
      s.occurrences.filter (fun a => compatible keys width bindings pattern a.2) := by
  cases hd : keys.needHead bindings pattern with
  | none => simp [query, hd, build, compatible]
  | some headKey =>
    cases arg : keys.needArgument bindings pattern with
    | none => simp [query, hd, arg, build, compatible, bucket_group, Function.comp_def]
    | some selection =>
      obtain ⟨i, key⟩ := selection
      by_cases indexed : i < width <;>
        simp [query, hd, arg, build, compatible, indexed, bucket_group, Function.comp_def]

omit [Hashable Head] [Hashable Argument] in
theorem successful_is_compatible (keys : IndexKeys M Head Argument) (width : ℕ)
    {bindings : B} {pattern : T} {value : V} {next : B}
    (hit : M.extend bindings pattern value = some next) :
    compatible keys width bindings pattern value = true := by
  cases hd : keys.needHead bindings pattern with
  | none => simp [compatible, hd]
  | some headKey =>
    have sameHead := keys.head_sound hit hd
    cases arg : keys.needArgument bindings pattern with
    | none => simp [compatible, hd, arg, sameHead]
    | some selection =>
      obtain ⟨i, key⟩ := selection
      have sameArgument := keys.argument_sound hit arg
      simp [compatible, hd, arg, sameHead, sameArgument]

def access (keys : IndexKeys M Head Argument) (width : ℕ) : CandidateAccess M where
  read s bindings pattern := query keys (build keys width s) bindings pattern
  selects s bindings pattern :=
    ⟨compatible keys width bindings pattern, query_eq_filter keys width s bindings pattern,
      fun _ _ hit => successful_is_compatible keys width hit⟩

theorem firings_exact [DecidableEq V] (keys : IndexKeys M Head Argument) (width : ℕ)
    (program : List (Rule T)) (s : Store V) :
    firingsUsing M (access keys width) program s = firings M program s :=
  firingsUsing_exact M (access keys width) program s

end OccurrenceIndex

end Mettapedia.Machines.TIsa.Derivation
