import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Rows

/-!
# The translation from the source, and its inverse on the image

`toTwin m s p` translates a pattern of the source at binder depth `m` into a twin term of sort `s`:
a bound name becomes the name variable of its pair, the drop of a bound name becomes the twin
variable, the drop of quoted code becomes `dropq`, and every other constructor its former.

* `toTwin_read`: on every twin term in a context of pairs the translation inverts the read-back;
  so the read-back is injective there (`read_injective`).
* `toTwin_closed`: the translation succeeds on every closed process of the source, and its result
  reads back to the process (with `represent_closed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT

mutual
  /-- **The translation** of a source pattern at binder depth `m`. -/
  def toTwin : (m : Nat) → (s : Srt) → Pattern → Option (G (pairs m) s)
    | m, .nm, .bvar i => if h : i < m then some (.var (nameAt m i h)) else none
    | m, .nm, .apply "NQuote" [p] => (toTwin m .pr p).map quoteT
    | _, .pr, .apply "PZero" [] => some zeroT
    | m, .pr, .apply "PDrop" [.bvar i] =>
        if h : i < m then some (.var (twinOf m (nameAt m i h))) else none
    | m, .pr, .apply "PDrop" [.apply "NQuote" [p]] => (toTwin m .pr p).map dropqT
    | m, .pr, .apply "PInput" [c, .lambda none b] =>
        match toTwin m .nm c, toTwin (m + 1) .pr b with
        | some c', some b' => some (inputT c' b')
        | _, _ => none
    | m, .pr, .apply "POutput" [c, p] =>
        match toTwin m .nm c, toTwin m .pr p with
        | some c', some p' => some (outputT c' p')
        | _, _ => none
    | m, .pr, .collection .hashBag es none => (toTwinList m es).map bagT
    | m, .ps, .collection .hashBag es none => toTwinList m es
    | _, _, _ => none

  /-- The translation of the components of a bag. -/
  def toTwinList : (m : Nat) → List Pattern → Option (G (pairs m) .ps)
    | _, [] => some pnilT
    | m, p :: ps =>
        match toTwin m .pr p, toTwinList m ps with
        | some t, some l => some (pconsT t l)
        | _, _ => none
end

/-- A name variable is the name variable of its pair. -/
theorem nameAt_half : ∀ (m : Nat) (v : Var (pairs m) .nm) (small : half (position v) < m),
    nameAt m (half (position v)) small = v
  | _ + 1, .zero, _ => rfl
  | m + 1, .succ (.succ w), small => by
      show Var.succ (Var.succ (nameAt m (half (position w)) _)) = _
      rw [nameAt_half m w]

/-- A twin variable is the twin of the name variable of its pair. -/
theorem twinOf_half : ∀ (m : Nat) (v : Var (pairs m) .pr) (small : half (position v) < m),
    twinOf m (nameAt m (half (position v)) small) = v
  | _ + 1, .succ .zero, _ => rfl
  | m + 1, .succ (.succ w), small => by
      show Var.succ (Var.succ (twinOf m (nameAt m (half (position w)) _))) = _
      rw [twinOf_half m w]

/-- **The translation inverts the read-back** on every term in a context of pairs. -/
theorem toTwin_read : ∀ {Γ : Ctx sig} {s : Srt} (t : G Γ s) (m : Nat) (shape : Γ = pairs m),
    toTwin m s (read t) = some (shape ▸ t)
  | _, s, .var v, m, shape => by
      subst shape
      obtain ⟨small, notList⟩ := var_pairs m v
      cases s with
      | nm =>
          show toTwin m .nm (.bvar (half (position v))) = _
          rw [toTwin, dif_pos small, nameAt_half]
      | pr =>
          show toTwin m .pr (.apply "PDrop" [.bvar (half (position v))]) = _
          rw [toTwin, dif_pos small, twinOf_half]
      | ps => exact absurd rfl notList
  | _, _, .op (.inl .zero) .nil, m, shape => by
      subst shape
      rfl
  | _, _, .op (.inl .bag) (.cons l .nil), m, shape => by
      have inner := toTwin_read l m shape
      subst shape
      obtain ⟨elements, same⟩ := read_ps_ground l
      rw [same] at inner
      show toTwin m .pr (read l) = _
      rw [same, toTwin]
      rw [toTwin] at inner
      rw [inner]
      rfl
  | _, _, .op (.inl .pnil) .nil, m, shape => by
      subst shape
      rfl
  | _, _, .op (.inl .pcons) (.cons p (.cons l .nil)), m, shape => by
      have head := toTwin_read p m shape
      have tail := toTwin_read l m shape
      subst shape
      obtain ⟨elements, same⟩ := read_ps_ground l
      rw [same, toTwin] at tail
      show toTwin m .ps (consBag (read p) (read l)) = _
      rw [same]
      show toTwinList m (read p :: elements) = _
      rw [toTwinList, head, tail]
  | _, _, .op (.inl .input) (.cons c (.cons b .nil)), m, shape => by
      have channel := toTwin_read c m shape
      have body := toTwin_read b (m + 1) (by rw [shape]; rfl)
      subst shape
      show toTwin m .pr (.apply "PInput" [read c, .lambda none (read b)]) = _
      rw [toTwin, channel, body]
  | _, _, .op (.inl .output) (.cons c (.cons p .nil)), m, shape => by
      have channel := toTwin_read c m shape
      have payload := toTwin_read p m shape
      subst shape
      show toTwin m .pr (.apply "POutput" [read c, read p]) = _
      rw [toTwin, channel, payload]
  | _, _, .op (.inl .dropq) (.cons p .nil), m, shape => by
      have inner := toTwin_read p m shape
      subst shape
      show toTwin m .pr (.apply "PDrop" [.apply "NQuote" [read p]]) = _
      rw [toTwin, inner]
      rfl
  | _, _, .op (.inl .quote) (.cons p .nil), m, shape => by
      have inner := toTwin_read p m shape
      subst shape
      show toTwin m .nm (.apply "NQuote" [read p]) = _
      rw [toTwin, inner]
      rfl
  | _, _, .op (.inr o) _, _, _ => o.key.elim

/-- **The read-back is injective** in a context of pairs. -/
theorem read_injective {m : Nat} {s : Srt} {t t' : G (pairs m) s} (same : read t = read t') :
    t = t' := by
  have first := toTwin_read t m rfl
  have second := toTwin_read t' m rfl
  rw [same] at first
  exact Option.some.inj (first.symm.trans second)

/-- **The translation succeeds on every closed process**, and the translated term reads back to
it. -/
theorem toTwin_closed (P : RhoProcess) : ∃ t : G [] .pr, toTwin 0 .pr P.1 = some t ∧ read t = P.1 := by
  obtain ⟨t, same⟩ := represent_closed P
  refine ⟨t, ?_, same⟩
  rw [← same]
  exact toTwin_read t 0 rfl

/-- Control: a pattern that is no process of the source has no translation. -/
theorem toTwin_refuses : toTwin 0 .pr (.bvar 0) = none := rfl

#print axioms toTwin_read
#print axioms read_injective
#print axioms toTwin_closed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation
