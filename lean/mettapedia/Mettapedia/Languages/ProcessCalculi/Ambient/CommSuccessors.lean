import Mettapedia.Languages.ProcessCalculi.Ambient.CommReflection

/-!
# The successors of an ambient process

`commSuccessors` lists the targets of the firings of mobile ambients with communication at a pattern:

- in a bag, an `open` beside the ambient it opens, an ambient holding `in m.P` beside the ambient `m`, and an input
  beside an output on its channel, each pair of members in order; and the firings of each member;
- in an ambient, a member ambient holding `out m.P`, `m` the enclosing ambient; and the firings of the content;
- under a restriction, the firings of the body.

Every firing's target is listed (`mem_commSuccessors`), so a process has finitely many firings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Comm

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (instantiateBVar)
open Mettapedia.Languages.ProcessCalculi.Ambient.Mobile (amb)

/-- An `open` of the second member by the first, the rest of the bag beside. -/
def openPair (rest : List Pattern) : Pattern → Pattern → Option Pattern
  | .apply "AOpen" [name, process], .apply "AAmb" [name', content] =>
      if name = name' then some (.collection .hashBag (process :: content :: rest) none) else none
  | _, _ => none

/-- An entry of the first member, an ambient holding `in m.P` at position `k`, into the second, the ambient `m`. -/
def enterAt (rest : List Pattern) (k : Nat) : Pattern → Pattern → Option Pattern
  | .apply "AAmb" [name, .collection .hashBag inner _], .apply "AAmb" [target', host] =>
      match inner[k]? with
      | some (.apply "AIn" [target, process]) =>
          if target = target' then
            some (.collection .hashBag (amb target' (.collection .hashBag
              [amb name (.collection .hashBag (process :: inner.eraseIdx k) none), host] none) :: rest) none)
          else none
      | _ => none
  | _, _ => none

/-- A communication of the first member, an input, with the second, an output on its channel. -/
def commPair (rest : List Pattern) : Pattern → Pattern → Option Pattern
  | .apply input [.lambda _ body], .apply output [message] =>
      if (input, output) ∈ channels then some (.collection .hashBag (instantiateBVar message body :: rest) none)
      else none
  | _, _ => none

/-- The number of members of an ambient's bag, and none otherwise. -/
def innerLength : Pattern → Nat
  | .apply "AAmb" [_, .collection .hashBag inner _] => inner.length
  | _ => 0

/-- The moves of two members of a bag. -/
def bagMoves (elements : List Pattern) : List Pattern :=
  (List.range elements.length).flatMap fun first =>
    (List.range (elements.length - 1)).flatMap fun second =>
      (openPair ((elements.eraseIdx first).eraseIdx second) (elements.getD first (.bvar 0))
          ((elements.eraseIdx first).getD second (.bvar 0))).toList ++
        (commPair ((elements.eraseIdx first).eraseIdx second) (elements.getD first (.bvar 0))
          ((elements.eraseIdx first).getD second (.bvar 0))).toList ++
        ((List.range (innerLength (elements.getD first (.bvar 0)))).filterMap fun k =>
          enterAt ((elements.eraseIdx first).eraseIdx second) k (elements.getD first (.bvar 0))
            ((elements.eraseIdx first).getD second (.bvar 0)))

/-- An exit of the member at `index`, an ambient holding `out parent.P` at position `k`, from the ambient `parent`. -/
def exitAt (parent : Pattern) (contents : List Pattern) (index k : Nat) : Option Pattern :=
  match contents.getD index (.bvar 0) with
  | .apply "AAmb" [name, .collection .hashBag inner _] =>
      match inner[k]? with
      | some (.apply "AOut" [parent', process]) =>
          if parent' = parent then
            some (.collection .hashBag [amb name (.collection .hashBag (process :: inner.eraseIdx k) none),
              amb parent (.collection .hashBag (contents.eraseIdx index) none)] none)
          else none
      | _ => none
  | _ => none

/-- The exits from an ambient. -/
def exitMoves (parent : Pattern) (contents : List Pattern) : List Pattern :=
  (List.range contents.length).flatMap fun index =>
    (List.range (innerLength (contents.getD index (.bvar 0)))).filterMap fun k => exitAt parent contents index k

/-- The exits from an ambient whose content is a bag. -/
def exitsOf (parent content : Pattern) : List Pattern :=
  match content with
  | .collection .hashBag contents _ => exitMoves parent contents
  | _ => []

mutual
  /-- **The successors of a pattern**, a list holding every target of a firing. -/
  def commSuccessors : Pattern → List Pattern
    | .collection .hashBag elements _ => bagMoves elements ++ insideSteps [] elements
    | .apply "AAmb" [parent, content] =>
        exitsOf parent content ++ (commSuccessors content).map (amb parent ·)
    | .apply "ANu" [.lambda _ body] => (commSuccessors body).map fun target => .apply "ANu" [.lambda none target]
    | _ => []

  /-- The firings of the members of a bag, the members before them already passed. -/
  def insideSteps (before : List Pattern) : List Pattern → List Pattern
    | [] => []
    | element :: after =>
        (commSuccessors element).map (fun target => .collection .hashBag (target :: (before ++ after)) none) ++
          insideSteps (before ++ [element]) after
end

theorem mem_insideSteps {target : Pattern} : ∀ (before elements : List Pattern) (index : Nat)
    (inside : index < elements.length), target ∈ commSuccessors elements[index] →
      .collection .hashBag (target :: (before ++ elements.eraseIdx index)) none ∈ insideSteps before elements
  | _, [], _, inside, _ => absurd inside (by simp)
  | before, element :: after, 0, _, member => by
      simp only [insideSteps, List.mem_append, List.mem_map]
      exact .inl ⟨target, member, by simp⟩
  | before, element :: after, index + 1, inside, member => by
      simp only [insideSteps, List.mem_append]
      refine .inr ?_
      have later := mem_insideSteps (before ++ [element]) after index (by simpa using inside) member
      simpa using later

theorem getD_of_lt {list : List Pattern} {index : Nat} (fallback : Pattern) (inside : index < list.length) :
    list.getD index fallback = list[index] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside]

/-- A pair of members of a bag, in order. -/
theorem mem_bagMoves_of {elements : List Pattern} {i j : Nat} (hi : i < elements.length)
    (hj : j < (elements.eraseIdx i).length) {target : Pattern}
    (listed : target ∈ (openPair ((elements.eraseIdx i).eraseIdx j) elements[i] (elements.eraseIdx i)[j]).toList ++
      (commPair ((elements.eraseIdx i).eraseIdx j) elements[i] (elements.eraseIdx i)[j]).toList ++
      ((List.range (innerLength elements[i])).filterMap fun k =>
        enterAt ((elements.eraseIdx i).eraseIdx j) k elements[i] (elements.eraseIdx i)[j])) :
    target ∈ bagMoves elements := by
  have firstIs : elements.getD i (.bvar 0) = elements[i] := getD_of_lt _ hi
  have secondIs : (elements.eraseIdx i).getD j (.bvar 0) = (elements.eraseIdx i)[j] := getD_of_lt _ hj
  have hj' : j < elements.length - 1 := by simpa [List.length_eraseIdx_of_lt hi] using hj
  simp only [bagMoves, List.mem_flatMap, List.mem_range]
  exact ⟨i, hi, j, hj', by rw [firstIs, secondIs]; exact listed⟩

/-- **Every firing's target is a successor.** -/
theorem mem_commSuccessors {source target : Pattern} (step : AmbCommRawStep source target) :
    target ∈ commSuccessors source := by
  induction step with
  | «open» i hi j hj name process content capability boundary =>
      rw [commSuccessors]
      refine List.mem_append_left _ (mem_bagMoves_of hi hj ?_)
      refine List.mem_append_left _ (List.mem_append_left _ ?_)
      rw [capability, boundary]
      simp [openPair, amb]
  | enter i hi j hj name target process host k hk mover capability destination =>
      rw [commSuccessors]
      refine List.mem_append_left _ (mem_bagMoves_of hi hj ?_)
      refine List.mem_append_right _ ?_
      rw [mover, destination]
      simp only [List.mem_filterMap, List.mem_range]
      refine ⟨k, by simpa [innerLength, amb] using hk, ?_⟩
      simp [enterAt, amb, List.getElem?_eq_getElem hk, capability]
  | exit i hi name parent process k hk mover capability =>
      rw [amb, commSuccessors]
      refine List.mem_append_left _ ?_
      simp only [exitsOf, exitMoves, List.mem_flatMap, List.mem_range, List.mem_filterMap]
      have atIndex := getD_of_lt (.bvar 0) hi
      refine ⟨i, hi, k, by rw [atIndex, mover]; simpa [innerLength, amb] using hk, ?_⟩
      unfold exitAt
      rw [atIndex, mover]
      simp [amb, List.getElem?_eq_getElem hk, capability]
  | comm listed i hi j hj binder body message receiving sending =>
      rw [commSuccessors]
      refine List.mem_append_left _ (mem_bagMoves_of hi hj ?_)
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      rw [receiving, sending]
      simp [commPair, listed]
  | @par elements tail i hi target inner recurse =>
      rw [commSuccessors]
      refine List.mem_append_right _ ?_
      simpa using mem_insideSteps [] elements i hi recurse
  | res binder inner recurse =>
      rw [commSuccessors]
      exact List.mem_map.mpr ⟨_, recurse, rfl⟩
  | ambient name inner recurse =>
      rw [amb, commSuccessors]
      refine List.mem_append_right _ ?_
      exact List.mem_map.mpr ⟨_, recurse, rfl⟩

/-! ## Every successor is a firing's target -/

theorem openPair_sound {elements : List Pattern} {tail : Option String} {i j : Nat} (hi : i < elements.length)
    (hj : j < (elements.eraseIdx i).length) {target : Pattern}
    (listed : openPair ((elements.eraseIdx i).eraseIdx j) elements[i] (elements.eraseIdx i)[j] = some target) :
    AmbCommRawStep (.collection .hashBag elements tail) target := by
  unfold openPair at listed
  split at listed
  · rename_i name process name' content firstIs secondIs
    split_ifs at listed with same
    cases listed
    subst same
    exact .open i hi j hj name process content firstIs secondIs
  · cases listed

theorem commPair_sound {elements : List Pattern} {tail : Option String} {i j : Nat} (hi : i < elements.length)
    (hj : j < (elements.eraseIdx i).length) {target : Pattern}
    (listed : commPair ((elements.eraseIdx i).eraseIdx j) elements[i] (elements.eraseIdx i)[j] = some target) :
    AmbCommRawStep (.collection .hashBag elements tail) target := by
  unfold commPair at listed
  split at listed
  · rename_i input binder body output message firstIs secondIs
    split_ifs at listed with paired
    cases listed
    exact .comm paired i hi j hj binder body message firstIs secondIs
  · cases listed

theorem enterAt_sound {elements : List Pattern} {tail : Option String} {i j k : Nat} (hi : i < elements.length)
    (hj : j < (elements.eraseIdx i).length) {target : Pattern}
    (listed : enterAt ((elements.eraseIdx i).eraseIdx j) k elements[i] (elements.eraseIdx i)[j] = some target) :
    AmbCommRawStep (.collection .hashBag elements tail) target := by
  unfold enterAt at listed
  split at listed
  · rename_i name inner innerTail target' host firstIs secondIs
    split at listed
    · rename_i destination process capabilityAt
      split_ifs at listed with same
      cases listed
      subst same
      obtain ⟨hk, capability⟩ := List.getElem?_eq_some_iff.mp capabilityAt
      exact .enter i hi j hj name destination process host k hk firstIs capability secondIs
    · cases listed
  · cases listed

theorem exitAt_sound {parent : Pattern} {contents : List Pattern} {tail : Option String} {index k : Nat}
    {target : Pattern} (listed : exitAt parent contents index k = some target) :
    AmbCommRawStep (amb parent (.collection .hashBag contents tail)) target := by
  unfold exitAt at listed
  split at listed
  · rename_i name inner innerTail moverAt
    split at listed
    · rename_i parent' process capabilityAt
      split_ifs at listed with same
      cases listed
      subst same
      have inside : index < contents.length := by
        by_contra outside
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at moverAt
        simp at moverAt
      rw [getD_of_lt _ inside] at moverAt
      obtain ⟨hk, capability⟩ := List.getElem?_eq_some_iff.mp capabilityAt
      exact .exit index inside name parent' process k hk moverAt capability
    · cases listed
  · cases listed

theorem of_mem_insideSteps {target : Pattern} : ∀ (before elements : List Pattern),
    target ∈ insideSteps before elements → ∃ (index : Nat) (inside : index < elements.length) (inner : Pattern),
      inner ∈ commSuccessors elements[index] ∧
        target = .collection .hashBag (inner :: (before ++ elements.eraseIdx index)) none
  | _, [], member => by simp [insideSteps] at member
  | before, element :: after, member => by
      simp only [insideSteps, List.mem_append, List.mem_map] at member
      rcases member with ⟨inner, innerMember, rfl⟩ | later
      · exact ⟨0, by simp, inner, innerMember, by simp⟩
      · obtain ⟨index, inside, inner, innerMember, rfl⟩ := of_mem_insideSteps (before ++ [element]) after later
        exact ⟨index + 1, by simpa using inside, inner, innerMember, by simp⟩

/-- **Every successor is the target of a firing.** -/
theorem commSuccessors_sound : ∀ (size : Nat) {source target : Pattern}, sizeOf source < size →
    target ∈ commSuccessors source → AmbCommRawStep source target
  | 0, _, _, small, _ => absurd small (Nat.not_lt_zero _)
  | size + 1, source, target, small, member => by
      unfold commSuccessors at member
      split at member
      · rename_i elements tail
        rcases List.mem_append.mp member with moved | inside
        · simp only [bagMoves, List.mem_flatMap, List.mem_range] at moved
          obtain ⟨i, hi, j, hj', listed⟩ := moved
          have hj : j < (elements.eraseIdx i).length := by simpa [List.length_eraseIdx_of_lt hi] using hj'
          rw [getD_of_lt _ hi, getD_of_lt _ hj] at listed
          simp only [List.mem_append, Option.mem_toList, List.mem_filterMap, List.mem_range]
            at listed
          rcases listed with (opened | communicated) | ⟨k, -, entered⟩
          · exact openPair_sound hi hj opened
          · exact commPair_sound hi hj communicated
          · exact enterAt_sound hi hj entered
        · obtain ⟨index, indexInside, inner, innerMember, rfl⟩ := of_mem_insideSteps [] elements inside
          have smaller : sizeOf elements[index] < size := by
            have inList := List.sizeOf_lt_of_mem (List.getElem_mem indexInside)
            simp only [Pattern.collection.sizeOf_spec] at small
            omega
          simpa using AmbCommRawStep.par (tail := tail) index indexInside
            (commSuccessors_sound size smaller innerMember)
      · rename_i parent content
        rcases List.mem_append.mp member with exited | inside
        · unfold exitsOf at exited
          split at exited
          · rename_i contents tail
            simp only [exitMoves, List.mem_flatMap, List.mem_range, List.mem_filterMap] at exited
            obtain ⟨index, -, k, -, listed⟩ := exited
            exact exitAt_sound listed
          · simp at exited
        · obtain ⟨inner, innerMember, rfl⟩ := List.mem_map.mp inside
          have smaller : sizeOf content < size := by
            simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec] at small
            omega
          exact .ambient parent (commSuccessors_sound size smaller innerMember)
      · rename_i binder body
        obtain ⟨inner, innerMember, rfl⟩ := List.mem_map.mp member
        have smaller : sizeOf body < size := by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega
        exact .res binder (commSuccessors_sound size smaller innerMember)
      · simp at member

end Mettapedia.Languages.ProcessCalculi.Ambient.Comm
