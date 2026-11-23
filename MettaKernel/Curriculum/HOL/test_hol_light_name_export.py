"""Check that the untrusted source adapter preserves OCaml name bytes."""

import json
from pathlib import Path
import shutil
import subprocess
import unittest


class SourceNameBytes(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if shutil.which("ocaml") is None:
            raise unittest.SkipTest("OCaml is required for source-adapter controls")
        source = Path(__file__).with_name("HOLLightProofClosure.ml").read_text()
        definition = "let hol_json_string" + source.split("let hol_json_string", 1)[1].split(";;", 1)[0] + ";;"
        program = definition + "\n" + """
for byte = 0 to 255 do
  print_endline ("PRIME_HOL_BYTE " ^ hol_json_string (String.make 1 (Char.chr byte)))
done;;
let names = [""; "x"; "x\\000"; "x\\255"; "\\128"; "\\255\\000"; "\\195\\169"; "\\233"];;
List.iter (fun name -> print_endline ("PRIME_HOL_NAME " ^ hol_json_string name)) names;;
List.iter (fun left -> List.iter (fun right ->
  Printf.printf "PRIME_HOL_ORDER %s %s %d\\n" (hol_json_string left)
    (hol_json_string right) (compare (String.compare left right) 0)) names) names;;
"""
        run = subprocess.run(["ocaml", "-noinit", "-noprompt"], input=program.encode(),
                             capture_output=True, check=True)
        if b"Error:" in run.stdout or b"Error:" in run.stderr:
            raise AssertionError(repr(run.stdout + run.stderr))
        cls.lines = [line.decode("utf-8") for line in run.stdout.splitlines()
                     if line.startswith(b"PRIME_HOL_")]

    def test_every_octet_is_one_exact_codepoint(self):
        names = [json.loads(line.removeprefix("PRIME_HOL_BYTE "))
                 for line in self.lines if line.startswith("PRIME_HOL_BYTE ")]
        self.assertEqual(len(names), 256)
        self.assertEqual(names, [chr(byte) for byte in range(256)])

    def test_escaped_and_non_utf8_names_remain_distinct(self):
        names = [json.loads(line.removeprefix("PRIME_HOL_NAME "))
                 for line in self.lines if line.startswith("PRIME_HOL_NAME ")]
        self.assertEqual(names, ["", "x", "x\x00", "x\xff", "\x80", "\xff\x00", "\xc3\xa9", "\xe9"])
        self.assertEqual(len(names), len(set(names)))

    def test_source_lexicographic_order_is_preserved(self):
        decoder = json.JSONDecoder()
        count = 0
        for line in self.lines:
            if not line.startswith("PRIME_HOL_ORDER "):
                continue
            remaining = line.removeprefix("PRIME_HOL_ORDER ")
            left, end = decoder.raw_decode(remaining)
            remaining = remaining[end:].lstrip()
            right, end = decoder.raw_decode(remaining)
            order = int(remaining[end:].strip())
            self.assertEqual(order, (left > right) - (left < right))
            count += 1
        self.assertEqual(count, 64)


if __name__ == "__main__":
    unittest.main()
