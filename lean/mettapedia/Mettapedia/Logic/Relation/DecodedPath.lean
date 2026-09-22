import Mathlib.Combinatorics.Quiver.Path

/-!
# Decoding finite lists of composable edges

An edge decoder supplies its endpoints and retained edge value. This module
checks that a list starts at the requested vertex and that consecutive edges
meet, producing Mathlib's indexed path. Concatenation agrees with path
composition, and a faithful edge encoding round-trips every directed path.
No edges are selected from a proposition or silently dropped.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Relation.DecodedPath

open Quiver

universe u v w
variable {V : Type u} [Quiver.{v} V] [DecidableEq V] {Code : Type w}

abbrev Edge (V : Type u) [Quiver.{v} V] := Σ source target : V, (source ⟶ target)

def decodeFrom (decode : Code → Option (Edge V)) (source : V) :
    List Code → Option (Σ target : V, Path source target)
  | [] => some ⟨source, .nil⟩
  | code :: rest => do
      let ⟨left, right, edge⟩ ← decode code
      if same : left = source then
        let ⟨target, tail⟩ ← decodeFrom decode right rest
        return ⟨target, (same ▸ edge).toPath.comp tail⟩
      else none

theorem decodeFrom_length (decode : Code → Option (Edge V))
    (source : V) (codes : List Code) (result : Σ target : V, Path source target)
    (computed : decodeFrom decode source codes = some result) :
    result.2.length = codes.length := by
  induction codes generalizing source with
  | nil => cases computed; rfl
  | cons code rest ih =>
      simp only [decodeFrom] at computed
      cases decoded : decode code with
      | none => simp [decoded] at computed
      | some edge =>
          obtain ⟨left, right, edge⟩ := edge
          simp only [decoded, bind, Option.bind] at computed
          split at computed
          · rename_i same
            subst left
            cases tailComputed : decodeFrom decode right rest with
            | none => simp [tailComputed] at computed
            | some tail =>
                simp only [tailComputed, pure, Option.some.injEq] at computed
                subst result
                simp only [Path.length_comp, Path.length_toPath, List.length_cons]
                rw [ih right tail tailComputed, Nat.add_comm]
          · contradiction

theorem decodeFrom_append (decode : Code → Option (Edge V))
    (source : V) (first second : List Code) :
    decodeFrom decode source (first ++ second) = do
      let ⟨middle, front⟩ ← decodeFrom decode source first
      let ⟨target, suffix⟩ ← decodeFrom decode middle second
      return ⟨target, front.comp suffix⟩ := by
  induction first generalizing source with
  | nil =>
      cases result : decodeFrom decode source second <;>
        simp [decodeFrom, result, Path.nil_comp]
  | cons code rest ih =>
      cases decoded : decode code with
      | none => simp [decodeFrom, decoded]
      | some edge =>
          obtain ⟨left, right, edge⟩ := edge
          by_cases same : left = source
          · subst left
            simp only [List.cons_append, decodeFrom, decoded, bind, Option.bind, ↓reduceDIte]
            rw [ih]
            cases frontComputed : decodeFrom decode right rest with
            | none => simp
            | some front =>
                obtain ⟨middle, front⟩ := front
                cases suffix : decodeFrom decode middle second <;>
                  simp [bind, Option.bind, pure, suffix, Path.comp_assoc]
          · simp [decodeFrom, decoded, same]

def encodePath (encode : {source target : V} → (source ⟶ target) → Code)
    {source target : V} (path : Path source target) : List Code :=
  match path with
  | .nil => []
  | .cons front edge => encodePath encode front ++ [encode edge]

theorem decodeFrom_encodePath
    (decode : Code → Option (Edge V))
    (encode : {source target : V} → (source ⟶ target) → Code)
    (roundTrip : ∀ {source target : V} (edge : source ⟶ target),
      decode (encode edge) = some ⟨source, target, edge⟩)
    {source target : V} (path : Path source target) :
    decodeFrom decode source (encodePath encode path) = some ⟨target, path⟩ := by
  induction path with
  | nil => rfl
  | @cons middle target front edge ih =>
      rw [encodePath, decodeFrom_append, ih]
      simp [decodeFrom, roundTrip, Path.comp]

omit [DecidableEq V] in
theorem encodePath_comp
    (encode : {source target : V} → (source ⟶ target) → Code)
    {source middle target : V} (first : Path source middle) (second : Path middle target) :
    encodePath encode (first.comp second) = encodePath encode first ++ encodePath encode second := by
  induction second with
  | nil => simp [encodePath]
  | cons path edge ih => simp [encodePath, ih, List.append_assoc]

/-- Successful decoding retains the exact input codes when the edge decoder
retains its input. This excludes dropping or deduplicating occurrences. -/
theorem encodePath_decodeFrom
    (decode : Code → Option (Edge V))
    (encode : {source target : V} → (source ⟶ target) → Code)
    (retains : ∀ (code : Code) (edge : Edge V), decode code = some edge → encode edge.2.2 = code)
    (source : V) (codes : List Code) (result : Σ target : V, Path source target)
    (computed : decodeFrom decode source codes = some result) :
    encodePath encode result.2 = codes := by
  induction codes generalizing source with
  | nil => cases computed; rfl
  | cons code rest ih =>
      simp only [decodeFrom] at computed
      cases decoded : decode code with
      | none => simp [decoded] at computed
      | some edge =>
          obtain ⟨left, right, edge⟩ := edge
          simp only [decoded, bind, Option.bind] at computed
          split at computed
          · rename_i same
            subst left
            cases tailComputed : decodeFrom decode right rest with
            | none => simp [tailComputed] at computed
            | some tail =>
                simp only [tailComputed, pure, Option.some.injEq] at computed
                subst result
                rw [encodePath_comp, ih right tail tailComputed]
                simp only [Hom.toPath, encodePath, List.nil_append,
                  retains code ⟨source, right, edge⟩ decoded, List.singleton_append]
          · contradiction

#print axioms decodeFrom_length
#print axioms decodeFrom_append
#print axioms decodeFrom_encodePath
#print axioms encodePath_decodeFrom

end Mettapedia.Logic.Relation.DecodedPath
