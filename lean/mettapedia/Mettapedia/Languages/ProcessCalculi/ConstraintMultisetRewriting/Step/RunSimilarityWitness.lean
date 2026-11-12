import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EscapeTransport

/-!
# Witnessed similarity of actual step runs

The existing similarity relation compares firings stage by stage. This data
type retains each chosen state isomorphism, including the final comparison.
Its propositional truncation is exactly that relation. The comparisons need
not be coherent execution squares: no equation between a later chosen map
and the result transport of an earlier map is imposed by `Similar`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} (T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P)

inductive SimilarityWitness : {s t : State} → P.Run s → P.Run t → Type (max uS uF uI)
  | nil {s t : State} (comparison : T.Iso s t) :
      SimilarityWitness (.nil s) (.nil t)
  | cons {s t : State} {first : Firing s} {second : Firing t}
      {accepted : P.Admits first} {accepted' : P.Admits second}
      {rest : P.Run (P.result first accepted)}
      {rest' : P.Run (P.result second accepted')}
      (comparison : T.Iso s t) (alike : T.Alike (T.move comparison first) second)
      (tail : SimilarityWitness rest rest') :
      SimilarityWitness (.cons first accepted rest) (.cons second accepted' rest')

namespace SimilarityWitness

variable {T}

theorem similar {s t : State} {first : P.Run s} {second : P.Run t}
    (witness : T.SimilarityWitness first second) : T.Similar first second := by
  induction witness with
  | nil comparison => exact ⟨comparison⟩
  | cons comparison alike _ ih => exact ⟨comparison, alike, ih⟩

theorem nonempty_iff {s t : State} (first : P.Run s) (second : P.Run t) :
    Nonempty (T.SimilarityWitness first second) ↔ T.Similar first second := by
  constructor
  · rintro ⟨witness⟩
    exact witness.similar
  · intro related
    induction first generalizing t with
    | nil s =>
        cases second with
        | nil t =>
            obtain ⟨comparison⟩ := related
            exact ⟨.nil comparison⟩
        | cons => exact False.elim related
    | cons firing accepted rest ih =>
        cases second with
        | nil => exact False.elim related
        | cons other accepted' rest' =>
            obtain ⟨comparison, alike, tail⟩ := related
            obtain ⟨witness⟩ := ih rest' tail
            exact ⟨.cons comparison alike witness⟩

def refl : {s : State} → (run : P.Run s) → T.SimilarityWitness run run
  | s, .nil _ => .nil (T.refl s)
  | s, .cons firing _ rest => .cons (T.refl s) (T.move_refl firing) (refl rest)

def symm : {s t : State} → {first : P.Run s} → {second : P.Run t} →
    T.SimilarityWitness first second → T.SimilarityWitness second first
  | _, _, _, _, .nil comparison => .nil (T.symm comparison)
  | _, _, .cons firing _ _, _, .cons comparison alike tail =>
      .cons (T.symm comparison)
        ((T.move_alike (T.symm comparison) alike).symm.trans (T.move_symm comparison firing))
        tail.symm

def trans : {s t u : State} → {first : P.Run s} → {second : P.Run t} → {third : P.Run u} →
    T.SimilarityWitness first second → T.SimilarityWitness second third →
      T.SimilarityWitness first third
  | _, _, _, _, _, _, .nil first, .nil second => .nil (T.trans first second)
  | _, _, _, .cons firing _ _, _, _, .cons first alike tail, .cons second alike' tail' =>
      .cons (T.trans first second)
        ((T.move_trans first second firing).trans ((T.move_alike second alike).trans alike'))
        (tail.trans tail')

def startIso : {s t : State} → {first : P.Run s} → {second : P.Run t} →
    T.SimilarityWitness first second → T.Iso s t
  | _, _, _, _, .nil comparison => comparison
  | _, _, _, _, .cons comparison _ _ => comparison

def lastIso : {s t : State} → {first : P.Run s} → {second : P.Run t} →
    T.SimilarityWitness first second → T.Iso first.last second.last
  | _, _, _, _, .nil comparison => comparison
  | _, _, _, _, .cons _ _ tail => tail.lastIso

def append : {s t : State} → {first : P.Run s} → {second : P.Run t} →
    T.SimilarityWitness first second →
      {later : P.Run first.last} → {later' : P.Run second.last} →
      T.SimilarityWitness later later' →
        T.SimilarityWitness (first.append later) (second.append later')
  | _, _, _, _, .nil _, _, _, later => later
  | _, _, _, _, .cons comparison alike tail, _, _, later =>
      .cons comparison alike (tail.append later)

def moveRun : {s t : State} → (comparison : T.Iso s t) → (run : P.Run s) →
    T.SimilarityWitness run (T.moveRun comparison run)
  | _, _, comparison, .nil _ => .nil comparison
  | _, _, comparison, .cons firing accepted rest =>
      .cons comparison (Alike.refl _) (moveRun (T.result_move comparison firing accepted) rest)

theorem length_eq {s t : State} {first : P.Run s} {second : P.Run t}
    (witness : T.SimilarityWitness first second) : first.word.length = second.word.length :=
  witness.similar.length_eq

/-- Similarity moves positions in order. It does not merge equal firings. -/
def events {s t : State} {first : P.Run s} {second : P.Run t}
    (witness : T.SimilarityWitness first second) :
    Fin first.word.length ≃ Fin second.word.length := finCongr witness.length_eq

theorem events_val {s t : State} {first : P.Run s} {second : P.Run t}
    (witness : T.SimilarityWitness first second) (event : Fin first.word.length) :
    (witness.events event).val = event.val := rfl

theorem events_trans {s t u : State} {first : P.Run s} {second : P.Run t} {third : P.Run u}
    (one : T.SimilarityWitness first second) (two : T.SimilarityWitness second third) :
    (one.trans two).events = one.events.trans two.events := by
  ext event
  rfl

theorem events_symm {s t : State} {first : P.Run s} {second : P.Run t}
    (witness : T.SimilarityWitness first second) : witness.symm.events = witness.events.symm := by
  ext event
  rfl

end SimilarityWitness

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.SimilarityWitness.nonempty_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.SimilarityWitness.events_trans
