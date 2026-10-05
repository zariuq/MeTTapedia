import Mettapedia.GSLT.LanguageDef.NativeOpsCLexSegments

/-! Literal token pieces checked by the shared C lexer. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.OrderedDependencyCPreparationTokens
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

private def reserve0 : String × List Token :=
  ("static bool space_module_link_reserve(Space ***items, uint32_t *capacity,\n                                       uint32_t required) {\n    if (required <= *capacity)\n", [.identifier "static".toList, .identifier "bool".toList, .identifier "space_module_link_reserve".toList, .punctuation "(".toList, .identifier "Space".toList, .punctuation "*".toList, .punctuation "*".toList, .punctuation "*".toList, .identifier "items".toList, .punctuation ",".toList, .identifier "uint32_t".toList, .punctuation "*".toList, .identifier "capacity".toList, .punctuation ",".toList, .identifier "uint32_t".toList, .identifier "required".toList, .punctuation ")".toList, .punctuation "{".toList, .identifier "if".toList, .punctuation "(".toList, .identifier "required".toList, .punctuation "<=".toList, .punctuation "*".toList, .identifier "capacity".toList, .punctuation ")".toList])

private theorem reserve0_scanned : reserve0.1.toList.foldl step initial = completed reserve0.2 :=
  by decide +kernel

private def reserve1 : String × List Token :=
  ("        return true;\n    uint32_t next = *capacity ? *capacity : 4u;\n    while (next < required) {\n", [.identifier "return".toList, .identifier "true".toList, .punctuation ";".toList, .identifier "uint32_t".toList, .identifier "next".toList, .punctuation "=".toList, .punctuation "*".toList, .identifier "capacity".toList, .punctuation "?".toList, .punctuation "*".toList, .identifier "capacity".toList, .punctuation ":".toList, .number "4u".toList, .punctuation ";".toList, .identifier "while".toList, .punctuation "(".toList, .identifier "next".toList, .punctuation "<".toList, .identifier "required".toList, .punctuation ")".toList, .punctuation "{".toList])

private theorem reserve1_scanned : reserve1.1.toList.foldl step initial = completed reserve1.2 :=
  by decide +kernel

private def reserve2 : String × List Token :=
  ("        if (next > UINT32_MAX / 2u) {\n            next = required;\n            break;\n", [.identifier "if".toList, .punctuation "(".toList, .identifier "next".toList, .punctuation ">".toList, .identifier "UINT32_MAX".toList, .punctuation "/".toList, .number "2u".toList, .punctuation ")".toList, .punctuation "{".toList, .identifier "next".toList, .punctuation "=".toList, .identifier "required".toList, .punctuation ";".toList, .identifier "break".toList, .punctuation ";".toList])

private theorem reserve2_scanned : reserve2.1.toList.foldl step initial = completed reserve2.2 :=
  by decide +kernel

private def reserve3 : String × List Token :=
  ("        }\n        next *= 2u;\n    }\n", [.punctuation "}".toList, .identifier "next".toList, .punctuation "*=".toList, .number "2u".toList, .punctuation ";".toList, .punctuation "}".toList])

private theorem reserve3_scanned : reserve3.1.toList.foldl step initial = completed reserve3.2 :=
  by decide +kernel

private def reserve4 : String × List Token :=
  ("    if ((uint64_t)next * sizeof(**items) > SIZE_MAX)\n        return false;\n    Space **grown = space_module_link_try_reallocate(*items, sizeof(**items) * (size_t)next);\n", [.identifier "if".toList, .punctuation "(".toList, .punctuation "(".toList, .identifier "uint64_t".toList, .punctuation ")".toList, .identifier "next".toList, .punctuation "*".toList, .identifier "sizeof".toList, .punctuation "(".toList, .punctuation "*".toList, .punctuation "*".toList, .identifier "items".toList, .punctuation ")".toList, .punctuation ">".toList, .identifier "SIZE_MAX".toList, .punctuation ")".toList, .identifier "return".toList, .identifier "false".toList, .punctuation ";".toList, .identifier "Space".toList, .punctuation "*".toList, .punctuation "*".toList, .identifier "grown".toList, .punctuation "=".toList, .identifier "space_module_link_try_reallocate".toList, .punctuation "(".toList, .punctuation "*".toList, .identifier "items".toList, .punctuation ",".toList, .identifier "sizeof".toList, .punctuation "(".toList, .punctuation "*".toList, .punctuation "*".toList, .identifier "items".toList, .punctuation ")".toList, .punctuation "*".toList, .punctuation "(".toList, .identifier "size_t".toList, .punctuation ")".toList, .identifier "next".toList, .punctuation ")".toList, .punctuation ";".toList])

private theorem reserve4_scanned : reserve4.1.toList.foldl step initial = completed reserve4.2 :=
  by decide +kernel

private def reserve5 : String × List Token :=
  ("    if (!grown)\n        return false;\n    *items = grown;\n", [.identifier "if".toList, .punctuation "(".toList, .punctuation "!".toList, .identifier "grown".toList, .punctuation ")".toList, .identifier "return".toList, .identifier "false".toList, .punctuation ";".toList, .punctuation "*".toList, .identifier "items".toList, .punctuation "=".toList, .identifier "grown".toList, .punctuation ";".toList])

private theorem reserve5_scanned : reserve5.1.toList.foldl step initial = completed reserve5.2 :=
  by decide +kernel

private def reserve6 : String × List Token :=
  ("    *capacity = next;\n    return true;\n}", [.punctuation "*".toList, .identifier "capacity".toList, .punctuation "=".toList, .identifier "next".toList, .punctuation ";".toList, .identifier "return".toList, .identifier "true".toList, .punctuation ";".toList, .punctuation "}".toList])

private theorem reserve6_scanned : reserve6.1.toList.foldl step initial = completed reserve6.2 :=
  by decide +kernel

def reservePieces : List (String × List Token) :=
  [reserve0, reserve1, reserve2, reserve3, reserve4, reserve5, reserve6]

def reserveTokens : List Token := reservePieces.flatMap Prod.snd

theorem reserve_lexed : lex (String.join (reservePieces.map Prod.fst)).toList =
    .ok reserveTokens := by
  apply lex_completed_string_pieces
  simp only [reservePieces, List.forall_cons]
  exact ⟨reserve0_scanned, ⟨reserve1_scanned, ⟨reserve2_scanned, ⟨reserve3_scanned, ⟨reserve4_scanned, ⟨reserve5_scanned, ⟨reserve6_scanned, True.intro⟩⟩⟩⟩⟩⟩⟩

#print axioms reserve_lexed

private def preparation0 : String × List Token :=
  ("static bool space_prepare_dependencies(\n        Space *importer, Space *const *dependencies, uint32_t count,\n        SpaceDependencyReservation *reservation) {\n", [.identifier "static".toList, .identifier "bool".toList, .identifier "space_prepare_dependencies".toList, .punctuation "(".toList, .identifier "Space".toList, .punctuation "*".toList, .identifier "importer".toList, .punctuation ",".toList, .identifier "Space".toList, .punctuation "*".toList, .identifier "const".toList, .punctuation "*".toList, .identifier "dependencies".toList, .punctuation ",".toList, .identifier "uint32_t".toList, .identifier "count".toList, .punctuation ",".toList, .identifier "SpaceDependencyReservation".toList, .punctuation "*".toList, .identifier "reservation".toList, .punctuation ")".toList, .punctuation "{".toList])

private theorem preparation0_scanned : preparation0.1.toList.foldl step initial = completed preparation0.2 :=
  by decide +kernel

private def preparation1 : String × List Token :=
  ("    *reservation = (SpaceDependencyReservation){0};\n    if (!importer || (count != 0u && !dependencies))\n        return false;\n", [.punctuation "*".toList, .identifier "reservation".toList, .punctuation "=".toList, .punctuation "(".toList, .identifier "SpaceDependencyReservation".toList, .punctuation ")".toList, .punctuation "{".toList, .number "0".toList, .punctuation "}".toList, .punctuation ";".toList, .identifier "if".toList, .punctuation "(".toList, .punctuation "!".toList, .identifier "importer".toList, .punctuation "||".toList, .punctuation "(".toList, .identifier "count".toList, .punctuation "!=".toList, .number "0u".toList, .punctuation "&&".toList, .punctuation "!".toList, .identifier "dependencies".toList, .punctuation ")".toList, .punctuation ")".toList, .identifier "return".toList, .identifier "false".toList, .punctuation ";".toList])

private theorem preparation1_scanned : preparation1.1.toList.foldl step initial = completed preparation1.2 :=
  by decide +kernel

private def preparation2 : String × List Token :=
  ("    bool has_new = false;\n    for (uint32_t i = 0u; i < count; i++) {\n        Space *dependency = dependencies[i];\n", [.identifier "bool".toList, .identifier "has_new".toList, .punctuation "=".toList, .identifier "false".toList, .punctuation ";".toList, .identifier "for".toList, .punctuation "(".toList, .identifier "uint32_t".toList, .identifier "i".toList, .punctuation "=".toList, .number "0u".toList, .punctuation ";".toList, .identifier "i".toList, .punctuation "<".toList, .identifier "count".toList, .punctuation ";".toList, .identifier "i".toList, .punctuation "++".toList, .punctuation ")".toList, .punctuation "{".toList, .identifier "Space".toList, .punctuation "*".toList, .identifier "dependency".toList, .punctuation "=".toList, .identifier "dependencies".toList, .punctuation "[".toList, .identifier "i".toList, .punctuation "]".toList, .punctuation ";".toList])

private theorem preparation2_scanned : preparation2.1.toList.foldl step initial = completed preparation2.2 :=
  by decide +kernel

private def preparation3 : String × List Token :=
  ("        if (!dependency || dependency == importer)\n            return false;\n        bool present = false;\n", [.identifier "if".toList, .punctuation "(".toList, .punctuation "!".toList, .identifier "dependency".toList, .punctuation "||".toList, .identifier "dependency".toList, .punctuation "==".toList, .identifier "importer".toList, .punctuation ")".toList, .identifier "return".toList, .identifier "false".toList, .punctuation ";".toList, .identifier "bool".toList, .identifier "present".toList, .punctuation "=".toList, .identifier "false".toList, .punctuation ";".toList])

private theorem preparation3_scanned : preparation3.1.toList.foldl step initial = completed preparation3.2 :=
  by decide +kernel

private def preparation4 : String × List Token :=
  ("        for (uint32_t j = 0u; j < importer->dep_count && !present; j++)\n            present = importer->deps[j] == dependency;\n        has_new |= !present;\n", [.identifier "for".toList, .punctuation "(".toList, .identifier "uint32_t".toList, .identifier "j".toList, .punctuation "=".toList, .number "0u".toList, .punctuation ";".toList, .identifier "j".toList, .punctuation "<".toList, .identifier "importer".toList, .punctuation "->".toList, .identifier "dep_count".toList, .punctuation "&&".toList, .punctuation "!".toList, .identifier "present".toList, .punctuation ";".toList, .identifier "j".toList, .punctuation "++".toList, .punctuation ")".toList, .identifier "present".toList, .punctuation "=".toList, .identifier "importer".toList, .punctuation "->".toList, .identifier "deps".toList, .punctuation "[".toList, .identifier "j".toList, .punctuation "]".toList, .punctuation "==".toList, .identifier "dependency".toList, .punctuation ";".toList, .identifier "has_new".toList, .punctuation "|=".toList, .punctuation "!".toList, .identifier "present".toList, .punctuation ";".toList])

private theorem preparation4_scanned : preparation4.1.toList.foldl step initial = completed preparation4.2 :=
  by decide +kernel

private def preparation5 : String × List Token :=
  ("    }\n    if (!has_new)\n        return true;\n", [.punctuation "}".toList, .identifier "if".toList, .punctuation "(".toList, .punctuation "!".toList, .identifier "has_new".toList, .punctuation ")".toList, .identifier "return".toList, .identifier "true".toList, .punctuation ";".toList])

private theorem preparation5_scanned : preparation5.1.toList.foldl step initial = completed preparation5.2 :=
  by decide +kernel

private def preparation6 : String × List Token :=
  ("    if ((uint64_t)count * sizeof(Space *) > SIZE_MAX)\n        return false;\n    Space **pending = space_module_link_try_reallocate(NULL, sizeof(*pending) * (size_t)count);\n", [.identifier "if".toList, .punctuation "(".toList, .punctuation "(".toList, .identifier "uint64_t".toList, .punctuation ")".toList, .identifier "count".toList, .punctuation "*".toList, .identifier "sizeof".toList, .punctuation "(".toList, .identifier "Space".toList, .punctuation "*".toList, .punctuation ")".toList, .punctuation ">".toList, .identifier "SIZE_MAX".toList, .punctuation ")".toList, .identifier "return".toList, .identifier "false".toList, .punctuation ";".toList, .identifier "Space".toList, .punctuation "*".toList, .punctuation "*".toList, .identifier "pending".toList, .punctuation "=".toList, .identifier "space_module_link_try_reallocate".toList, .punctuation "(".toList, .identifier "NULL".toList, .punctuation ",".toList, .identifier "sizeof".toList, .punctuation "(".toList, .punctuation "*".toList, .identifier "pending".toList, .punctuation ")".toList, .punctuation "*".toList, .punctuation "(".toList, .identifier "size_t".toList, .punctuation ")".toList, .identifier "count".toList, .punctuation ")".toList, .punctuation ";".toList])

private theorem preparation6_scanned : preparation6.1.toList.foldl step initial = completed preparation6.2 :=
  by decide +kernel

private def preparation7 : String × List Token :=
  ("    if (!pending)\n        return false;\n    uint32_t added = 0u;\n", [.identifier "if".toList, .punctuation "(".toList, .punctuation "!".toList, .identifier "pending".toList, .punctuation ")".toList, .identifier "return".toList, .identifier "false".toList, .punctuation ";".toList, .identifier "uint32_t".toList, .identifier "added".toList, .punctuation "=".toList, .number "0u".toList, .punctuation ";".toList])

private theorem preparation7_scanned : preparation7.1.toList.foldl step initial = completed preparation7.2 :=
  by decide +kernel

private def preparation8 : String × List Token :=
  ("    bool ok = true;\n    for (uint32_t i = 0u; ok && i < count; i++) {\n        Space *dependency = dependencies[i];\n", [.identifier "bool".toList, .identifier "ok".toList, .punctuation "=".toList, .identifier "true".toList, .punctuation ";".toList, .identifier "for".toList, .punctuation "(".toList, .identifier "uint32_t".toList, .identifier "i".toList, .punctuation "=".toList, .number "0u".toList, .punctuation ";".toList, .identifier "ok".toList, .punctuation "&&".toList, .identifier "i".toList, .punctuation "<".toList, .identifier "count".toList, .punctuation ";".toList, .identifier "i".toList, .punctuation "++".toList, .punctuation ")".toList, .punctuation "{".toList, .identifier "Space".toList, .punctuation "*".toList, .identifier "dependency".toList, .punctuation "=".toList, .identifier "dependencies".toList, .punctuation "[".toList, .identifier "i".toList, .punctuation "]".toList, .punctuation ";".toList])

private theorem preparation8_scanned : preparation8.1.toList.foldl step initial = completed preparation8.2 :=
  by decide +kernel

private def preparation9 : String × List Token :=
  ("        if (!dependency || dependency == importer) {\n            ok = false;\n            break;\n", [.identifier "if".toList, .punctuation "(".toList, .punctuation "!".toList, .identifier "dependency".toList, .punctuation "||".toList, .identifier "dependency".toList, .punctuation "==".toList, .identifier "importer".toList, .punctuation ")".toList, .punctuation "{".toList, .identifier "ok".toList, .punctuation "=".toList, .identifier "false".toList, .punctuation ";".toList, .identifier "break".toList, .punctuation ";".toList])

private theorem preparation9_scanned : preparation9.1.toList.foldl step initial = completed preparation9.2 :=
  by decide +kernel

private def preparation10 : String × List Token :=
  ("        }\n        bool present = false;\n        for (uint32_t j = 0u; j < importer->dep_count && !present; j++)\n", [.punctuation "}".toList, .identifier "bool".toList, .identifier "present".toList, .punctuation "=".toList, .identifier "false".toList, .punctuation ";".toList, .identifier "for".toList, .punctuation "(".toList, .identifier "uint32_t".toList, .identifier "j".toList, .punctuation "=".toList, .number "0u".toList, .punctuation ";".toList, .identifier "j".toList, .punctuation "<".toList, .identifier "importer".toList, .punctuation "->".toList, .identifier "dep_count".toList, .punctuation "&&".toList, .punctuation "!".toList, .identifier "present".toList, .punctuation ";".toList, .identifier "j".toList, .punctuation "++".toList, .punctuation ")".toList])

private theorem preparation10_scanned : preparation10.1.toList.foldl step initial = completed preparation10.2 :=
  by decide +kernel

private def preparation11 : String × List Token :=
  ("            present = importer->deps[j] == dependency;\n        for (uint32_t j = 0u; j < added && !present; j++)\n            present = pending[j] == dependency;\n", [.identifier "present".toList, .punctuation "=".toList, .identifier "importer".toList, .punctuation "->".toList, .identifier "deps".toList, .punctuation "[".toList, .identifier "j".toList, .punctuation "]".toList, .punctuation "==".toList, .identifier "dependency".toList, .punctuation ";".toList, .identifier "for".toList, .punctuation "(".toList, .identifier "uint32_t".toList, .identifier "j".toList, .punctuation "=".toList, .number "0u".toList, .punctuation ";".toList, .identifier "j".toList, .punctuation "<".toList, .identifier "added".toList, .punctuation "&&".toList, .punctuation "!".toList, .identifier "present".toList, .punctuation ";".toList, .identifier "j".toList, .punctuation "++".toList, .punctuation ")".toList, .identifier "present".toList, .punctuation "=".toList, .identifier "pending".toList, .punctuation "[".toList, .identifier "j".toList, .punctuation "]".toList, .punctuation "==".toList, .identifier "dependency".toList, .punctuation ";".toList])

private theorem preparation11_scanned : preparation11.1.toList.foldl step initial = completed preparation11.2 :=
  by decide +kernel

private def preparation12 : String × List Token :=
  ("        if (!present)\n            pending[added++] = dependency;\n    }\n", [.identifier "if".toList, .punctuation "(".toList, .punctuation "!".toList, .identifier "present".toList, .punctuation ")".toList, .identifier "pending".toList, .punctuation "[".toList, .identifier "added".toList, .punctuation "++".toList, .punctuation "]".toList, .punctuation "=".toList, .identifier "dependency".toList, .punctuation ";".toList, .punctuation "}".toList])

private theorem preparation12_scanned : preparation12.1.toList.foldl step initial = completed preparation12.2 :=
  by decide +kernel

private def preparation13 : String × List Token :=
  ("    ok = ok && added <= UINT32_MAX - importer->dep_count &&\n        space_module_link_reserve(&importer->deps, &importer->dep_cap,\n                                  importer->dep_count + added);\n", [.identifier "ok".toList, .punctuation "=".toList, .identifier "ok".toList, .punctuation "&&".toList, .identifier "added".toList, .punctuation "<=".toList, .identifier "UINT32_MAX".toList, .punctuation "-".toList, .identifier "importer".toList, .punctuation "->".toList, .identifier "dep_count".toList, .punctuation "&&".toList, .identifier "space_module_link_reserve".toList, .punctuation "(".toList, .punctuation "&".toList, .identifier "importer".toList, .punctuation "->".toList, .identifier "deps".toList, .punctuation ",".toList, .punctuation "&".toList, .identifier "importer".toList, .punctuation "->".toList, .identifier "dep_cap".toList, .punctuation ",".toList, .identifier "importer".toList, .punctuation "->".toList, .identifier "dep_count".toList, .punctuation "+".toList, .identifier "added".toList, .punctuation ")".toList, .punctuation ";".toList])

private theorem preparation13_scanned : preparation13.1.toList.foldl step initial = completed preparation13.2 :=
  by decide +kernel

private def preparation14 : String × List Token :=
  ("    for (uint32_t i = 0u; ok && i < added; i++) {\n        Space *dependency = pending[i];\n        ok = dependency->importer_count != UINT32_MAX &&\n", [.identifier "for".toList, .punctuation "(".toList, .identifier "uint32_t".toList, .identifier "i".toList, .punctuation "=".toList, .number "0u".toList, .punctuation ";".toList, .identifier "ok".toList, .punctuation "&&".toList, .identifier "i".toList, .punctuation "<".toList, .identifier "added".toList, .punctuation ";".toList, .identifier "i".toList, .punctuation "++".toList, .punctuation ")".toList, .punctuation "{".toList, .identifier "Space".toList, .punctuation "*".toList, .identifier "dependency".toList, .punctuation "=".toList, .identifier "pending".toList, .punctuation "[".toList, .identifier "i".toList, .punctuation "]".toList, .punctuation ";".toList, .identifier "ok".toList, .punctuation "=".toList, .identifier "dependency".toList, .punctuation "->".toList, .identifier "importer_count".toList, .punctuation "!=".toList, .identifier "UINT32_MAX".toList, .punctuation "&&".toList])

private theorem preparation14_scanned : preparation14.1.toList.foldl step initial = completed preparation14.2 :=
  by decide +kernel

private def preparation15 : String × List Token :=
  ("            space_module_link_reserve(&dependency->importers, &dependency->importer_cap,\n                                      dependency->importer_count + 1u);\n    }\n", [.identifier "space_module_link_reserve".toList, .punctuation "(".toList, .punctuation "&".toList, .identifier "dependency".toList, .punctuation "->".toList, .identifier "importers".toList, .punctuation ",".toList, .punctuation "&".toList, .identifier "dependency".toList, .punctuation "->".toList, .identifier "importer_cap".toList, .punctuation ",".toList, .identifier "dependency".toList, .punctuation "->".toList, .identifier "importer_count".toList, .punctuation "+".toList, .number "1u".toList, .punctuation ")".toList, .punctuation ";".toList, .punctuation "}".toList])

private theorem preparation15_scanned : preparation15.1.toList.foldl step initial = completed preparation15.2 :=
  by decide +kernel

private def preparation16 : String × List Token :=
  ("    if (!ok) {\n        free(pending);\n        return false;\n", [.identifier "if".toList, .punctuation "(".toList, .punctuation "!".toList, .identifier "ok".toList, .punctuation ")".toList, .punctuation "{".toList, .identifier "free".toList, .punctuation "(".toList, .identifier "pending".toList, .punctuation ")".toList, .punctuation ";".toList, .identifier "return".toList, .identifier "false".toList, .punctuation ";".toList])

private theorem preparation16_scanned : preparation16.1.toList.foldl step initial = completed preparation16.2 :=
  by decide +kernel

private def preparation17 : String × List Token :=
  ("    }\n    *reservation = (SpaceDependencyReservation){pending, added};\n    return true;\n", [.punctuation "}".toList, .punctuation "*".toList, .identifier "reservation".toList, .punctuation "=".toList, .punctuation "(".toList, .identifier "SpaceDependencyReservation".toList, .punctuation ")".toList, .punctuation "{".toList, .identifier "pending".toList, .punctuation ",".toList, .identifier "added".toList, .punctuation "}".toList, .punctuation ";".toList, .identifier "return".toList, .identifier "true".toList, .punctuation ";".toList])

private theorem preparation17_scanned : preparation17.1.toList.foldl step initial = completed preparation17.2 :=
  by decide +kernel

private def preparation18 : String × List Token :=
  ("}", [.punctuation "}".toList])

private theorem preparation18_scanned : preparation18.1.toList.foldl step initial = completed preparation18.2 :=
  by decide +kernel

def preparationPieces : List (String × List Token) :=
  [preparation0, preparation1, preparation2, preparation3, preparation4, preparation5, preparation6, preparation7, preparation8, preparation9, preparation10, preparation11, preparation12, preparation13, preparation14, preparation15, preparation16, preparation17, preparation18]

def preparationTokens : List Token := preparationPieces.flatMap Prod.snd

theorem preparation_lexed : lex (String.join (preparationPieces.map Prod.fst)).toList =
    .ok preparationTokens := by
  apply lex_completed_string_pieces
  simp only [preparationPieces, List.forall_cons]
  exact ⟨preparation0_scanned, ⟨preparation1_scanned, ⟨preparation2_scanned, ⟨preparation3_scanned, ⟨preparation4_scanned, ⟨preparation5_scanned, ⟨preparation6_scanned, ⟨preparation7_scanned, ⟨preparation8_scanned, ⟨preparation9_scanned, ⟨preparation10_scanned, ⟨preparation11_scanned, ⟨preparation12_scanned, ⟨preparation13_scanned, ⟨preparation14_scanned, ⟨preparation15_scanned, ⟨preparation16_scanned, ⟨preparation17_scanned, ⟨preparation18_scanned, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

#print axioms preparation_lexed

end Mettapedia.Machines.OrderedDependencyCPreparationTokens
