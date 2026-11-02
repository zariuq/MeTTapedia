import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingNormal
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationSettle

/-!
# Enough fuel settles the reading

Every step of reading back goes to something lighter: a block to its components, the components at a place to one of
them among the others, a marker to the components placed elsewhere, a capability, a prefix by a capability term, an
input or a replication to its own block.
With fuel past three times the weight, more fuel changes nothing (`decode_settle`), so two readings with enough fuel
agree (`decodeForm_settled`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex decompose size sizeList mass_decompose)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedBlock locatedRepBlock)

theorem sizeList_filter_add (keep : Pattern → Bool) :
    ∀ components : List Pattern,
      sizeList (components.filter keep) + sizeList (components.filter fun component => !keep component) =
        sizeList components
  | [] => rfl
  | component :: rest => by
      have recurse := sizeList_filter_add keep rest
      by_cases kept : keep component = true
      · simp [kept, sizeList]
        omega
      · simp [kept, sizeList]
        omega

theorem size_le_sizeList {component : Pattern} : ∀ {components : List Pattern}, component ∈ components →
    size component ≤ sizeList components
  | _ :: rest, member => by
      rcases List.mem_cons.mp member with rfl | inRest
      · simp [sizeList]
      · have := size_le_sizeList inRest
        simp only [sizeList]
        omega

/-- A component placed at a place weighs, with those placed elsewhere, no more than the whole list. -/
theorem size_add_elsewhere {place component : Pattern} {components : List Pattern}
    (member : component ∈ components.filter (placedAt place)) :
    size component + sizeList (components.filter fun other => !placedAt place other) ≤ sizeList components := by
  have split := sizeList_filter_add (placedAt place) components
  have here := size_le_sizeList member
  omega

theorem size_pos (pattern : Pattern) : 1 ≤ size pattern := by
  cases pattern <;> simp [size]

/-- **More fuel changes no reading past three times its weight.** -/
theorem decode_settle : ∀ (fuel : Nat),
    (∀ (place : Pattern) (components : List Pattern), 3 * sizeList components + 2 ≤ fuel →
      readPlaced fuel place components = readPlaced (fuel + 1) place components) ∧
    (∀ (place : Pattern) (form : Prenex), 3 * form.mass + 3 ≤ fuel →
      decodeForm fuel place form = decodeForm (fuel + 1) place form) ∧
    (∀ (place component : Pattern) (elsewhere : List Pattern), 3 * (size component + sizeList elsewhere) + 1 ≤ fuel →
      readComponent fuel place component elsewhere = readComponent (fuel + 1) place component elsewhere)
  | 0 => ⟨fun _ _ heavy => by omega, fun _ _ heavy => by omega, fun _ _ _ heavy => by omega⟩
  | fuel + 1 => by
      obtain ⟨placedBelow, formsBelow, componentBelow⟩ := decode_settle fuel
      refine ⟨fun place components heavy => ?_, fun place form heavy => ?_,
        fun place component elsewhere heavy => ?_⟩
      · rw [readPlaced_succ, readPlaced_succ]
        refine List.map_congr_left fun component member => componentBelow place component _ ?_
        have := size_add_elsewhere member
        omega
      · obtain ⟨count, components⟩ := form
        simp only [decodeForm]
        congr 1
        refine placedBelow _ _ ?_
        simp only [Prenex.mass] at heavy
        omega
      · cases component with
        | apply label arguments =>
            match arguments, heavy with
            | [_, second, third], heavy =>
                simp only [size, sizeList] at heavy
                simp only [readComponent]
                split_ifs
                · rw [placedBelow second elsewhere (by omega)]
                all_goals first
                  | rfl
                  | have weight := mass_decompose (block := locatedBlock) third
                    rw [formsBelow place _ (by omega)]
            | [_, second], heavy =>
                simp only [size, sizeList] at heavy
                simp only [readComponent]
                split_ifs
                · cases second with
                  | lambda binder body =>
                      have weight := mass_decompose (block := locatedBlock) body
                      simp only [size] at heavy
                      simp only
                      rw [formsBelow _ _ (by omega)]
                  | _ => rfl
                all_goals rfl
            | [argument], heavy =>
                simp only [size, sizeList] at heavy
                simp only [readComponent]
                split_ifs
                · have weight := mass_decompose (block := locatedBlock) argument
                  rw [formsBelow place _ (by omega)]
                · rfl
            | [], _ => rfl
            | _ :: _ :: _ :: _ :: _, _ => rfl
        | _ => rfl

/-- **Two readings with enough fuel agree.** -/
theorem decodeForm_settled {first second : Nat} (place : Pattern) (form : Prenex)
    (firstEnough : 3 * form.mass + 3 ≤ first) (secondEnough : 3 * form.mass + 3 ≤ second) :
    decodeForm first place form = decodeForm second place form := by
  have stable : ∀ extra fuel, 3 * form.mass + 3 ≤ fuel → decodeForm fuel place form = decodeForm (fuel + extra) place form := by
    intro extra
    induction extra with
    | zero => intro fuel _; rfl
    | succ extra recurse =>
        intro fuel enough
        rw [recurse fuel enough, (decode_settle (fuel + extra)).2.1 place form (by omega)]
        rfl
  rcases Nat.le_total first second with order | order
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
    exact stable extra first firstEnough
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
    exact (stable extra second secondEnough).symm

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
