import Mettapedia.GSLT.LanguageDef.LiveModuleEdits
import Mettapedia.Languages.MeTTa.SpaceTheory.Presentation
import Mettapedia.Languages.MeTTa.HE.Space
import Mettapedia.Languages.MeTTa.PeTTa.Effects

/-! An explicitly selected constructor-language interpretation of a space.
Ordinary MeTTa data are not normalized in storage. An open equation, an
unrepresented declaration or a malformed reserved form cannot silently
become an inert atom in this interpretation. The two insertion instances use
the existing space models, not a shared definition of dialect evaluation. -/
set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.SpaceTheory.LiteralRealization

open Mettapedia.OSLF.MeTTaIL.Syntax (LanguageDef Pattern)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.GSLT.LanguageDef.LiveModuleEdits
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Atoms (Content content)

/-- Specialization to literal definitions and single definitional
equations. The contribution is the one in the space presentation;
the occurrence number is only part of the authored diagnostic name. -/
def decode (i : Nat) (a : Atom) : Option (Edit Atom) :=
  let name := "space:" ++ toString i
  match content a with
  | .definition l r => do
    let part ← Presentation.contribution? .literal (.definition l r)
    let [rule] := part.rewrites | none
    return .rule { rule with name }
  | .equation .indifferent first second [] => do
    let part ← Presentation.contribution? .literal (.equation .indifferent first second [])
    let [eq] := part.equations | none
    return .equation { eq with name }
  | .data _ => some (.datum a)
  | _ => none

def readEvents (start : Nat) : List Atom → Option (List (Edit Atom))
  | [] => some []
  | a :: more => do
    let event ← decode start a
    let rest ← readEvents (start+1) more
    return event :: rest

private theorem readEvents_snoc (start : Nat) (atoms : List Atom) (a : Atom) {es e}
    (old : readEvents start atoms = some es) (added : decode (start + atoms.length) a = some e) :
    readEvents start (atoms ++ [a]) = some (es ++ [e]) := by
  induction atoms generalizing start es with
  | nil =>
    obtain rfl := Option.some.inj old
    have found : decode start a = some e := by simpa using added
    simp [readEvents, found]
  | cons first tail ih =>
    cases atHead : decode start first with
    | none => simp [readEvents, atHead] at old
    | some v =>
      cases atTail : readEvents (start+1) tail with
      | none => simp [readEvents, atHead, atTail] at old
      | some vs =>
        simp [readEvents, atHead, atTail] at old
        subst es
        have last : decode ((start+1) + tail.length) a = some e := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using added
        simp [readEvents, atHead, ih _ atTail last]

def history (o : Order) (atoms : List Atom) : List Atom :=
  match o with
  | .front => atoms.reverse
  | .back => atoms

private theorem history_add (o : Order) (a : Atom) (rs : List Atom) :
    history o (o.insert a rs) = history o rs ++ [a] := by cases o <;> simp [Order.insert, history]

/-- Batch interpretation of the physical atoms above a fixed authored base.
It neither reads nor updates an index. -/
def view? (o : Order) (base : LanguageDef) (rs : List Atom) : Option LanguageDef :=
  (readEvents 0 (history o rs)).map (resulting o base)

theorem view_after_insert (o : Order) (base : LanguageDef) (rs : List Atom) (a : Atom)
    {l e} (before : view? o base rs = some l) (added : decode rs.length a = some e) :
    view? o base (o.insert a rs) = some (publish o l e) := by
  unfold view? at before ⊢
  cases parsed : readEvents 0 (history o rs) with
  | none => simp [parsed] at before
  | some es =>
    simp [parsed] at before
    subst l
    have found : decode (0 + (history o rs).length) a = some e := by
      cases o <;> simpa [history] using added
    rw [history_add, readEvents_snoc _ _ _ parsed found]
    simp [resulting, List.foldl_append]

noncomputable def reference? (premises : BasePremiseEvaluator) (o : Order) (base : LanguageDef)
    (rs : List Atom) (q : Pattern) :=
  (view? o base rs).map fun l =>
    Mettapedia.GSLT.Contracts.ScopedAliasDispatch.moduloRead premises l (·.left) q l.rewrites

/-- After the raw insertion, reading from scratch and updating the prior
materialized view agree on all ordered ground-key queries in the slice. -/
theorem lookup_after_insert (premises : BasePremiseEvaluator) (o : Order) (base : LanguageDef)
    (rs : List Atom) (a : Atom) {l e} (before : view? o base rs = some l)
    (added : decode rs.length a = some e) (valid : admitted l = true)
    (keys : Keys l) (correct : keys = build l) {out} (installed : update? o l keys e = some out)
    (q : Pattern) :
    reference? premises o base (o.insert a rs) q = some (answers (publish o l e) out q) := by
  obtain ⟨accepted, rfl⟩ := update_exact o l valid keys correct e installed
  rw [reference?, view_after_insert o base rs a before added, Option.map_some, answers_build _ _ accepted]

/-- The HE list model prepends. This is that traversal profile, not a
language-wide order guarantee for HE. -/
theorem he_add (premises : BasePremiseEvaluator) (base : LanguageDef) (s : HE.Space) (a : Atom)
    {l e} (before : view? .front base s.atoms = some l) (added : decode s.atoms.length a = some e)
    (valid : admitted l = true) (keys : Keys l) (correct : keys = build l) {out}
    (installed : update? .front l keys e = some out) (q : Pattern) :
    reference? premises .front base (s.add a).atoms q = some (answers (publish .front l e) out q) :=
  lookup_after_insert premises .front base s.atoms a before added valid keys correct installed q

/-- PeTTa insertion at a readable handle appends. Observe *that handle* in
the actual successor store, not a synthetic copy in the other dialect. -/
theorem petta_insert (premises : BasePremiseEvaluator) (base : LanguageDef)
    (s after : PeTTa.Effects.State) (h : PeTTa.NamedSpaces.Handle) (a : Atom)
    (inserted : PeTTa.Effects.insert s h a = some after) (rs : List Atom) (reads : s.read h = some rs)
    {l e} (before : view? .back base rs = some l) (added : decode rs.length a = some e)
    (valid : admitted l = true) (keys : Keys l) (correct : keys = build l) {out}
    (installed : update? .back l keys e = some out) (q : Pattern) :
    (after.read h).bind (fun next => reference? premises .back base next q) =
      some (answers (publish .back l e) out q) := by
  obtain ⟨was, old, fresh⟩ := PeTTa.Effects.insert_reads_back inserted
  have eq := Option.some.inj (old.symm.trans reads)
  subst was
  rw [fresh, Option.bind_some]
  exact lookup_after_insert premises .back base rs a before added valid keys correct installed q

end Mettapedia.Languages.MeTTa.SpaceTheory.LiteralRealization
