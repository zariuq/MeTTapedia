from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from measure_source import index_length, index_length_sum, measure, successor_bytes


def index_text(value):
    prefix, digits = value // 20, []
    while prefix:
        digit = (prefix - 1) % 5 + 1
        prefix = (prefix - digit) // 5
        digits.append(digit)
    body = "".join(f"(mm-cons (mm-nat {digit}) " for digit in digits)
    body += "(mm-nil)" + ")" * len(digits)
    return f"(mm-compressed-index-code {body} (mm-nat {value % 20}))"


def string_text(value):
    body = "".join(f"(mm-char-cons (mm-nat {ord(char)}) " for char in value)
    return "(mm-string " + body + "(mm-char-nil)" + ")" * (len(value) + 1)


class SourceMeasurementTests(unittest.TestCase):
    def test_index_byte_sums_at_every_prefix_boundary(self):
        for count in (0, 1, 19, 20, 21, 119, 120, 121, 619, 620, 621, 3120, 9863):
            self.assertEqual(index_length_sum(count), sum(len(index_text(i)) for i in range(count)))
        for value in (0, 19, 20, 119, 120, 619, 620, 3119, 3120, 9863):
            self.assertEqual(index_length(value), len(index_text(value)))

    def test_successor_byte_formula_matches_small_rows(self):
        owner, position = "proof λ", 1234
        proof = f"(mm-source-proof-owner {string_text(owner)} (mm-nat {position}))"
        for tag in (None, "mm-compressed-heap-owner", "mm-compressed-node-owner",
                    "mm-compressed-stack-owner"):
            for count in (0, 1, 20, 121):
                prefix = "mm-compressed-index-successor" if tag else "mm-index-successor"
                wrapped = f"({tag} {proof})" if tag else proof
                rows = [f"({prefix} {wrapped} {index_text(i)} {index_text(i + 1)})\n"
                        for i in range(count)]
                self.assertEqual(successor_bytes(count, position, tag, owner),
                                 sum(len(row.encode("utf-8")) for row in rows))

    def test_payload_bounds_and_scope_restore(self):
        source = (b"$c wff |- $.\n$v x $.\nwf $f wff x $.\nax $a |- x $.\n"
                  b"${ h $e |- x $.\ncompact $p |- x $= ( ax ) AA? $. $}\n"
                  b"normal $p |- x $= wf ax $.\n")
        result = measure(source)
        self.assertEqual(result["source_forms_in_file"], 9)
        self.assertEqual(result["counts"]["compressed_theorems"], 1)
        self.assertEqual(result["payload"]["compressed_body_bytes"], 3)
        self.assertEqual(result["payload"]["compressed_header_labels"], 1)
        self.assertEqual(result["payload"]["normal_prefix_inventory_rows"], 3)
        self.assertEqual(sum(result["successor_rows_lower"].values()), 15)
        self.assertEqual(sum(result["successor_rows_upper"].values()), 19)

    def test_includes_do_not_claim_expanded_upper_bounds(self):
        result = measure(b"$[ child.mm $]\n")
        self.assertIsNone(result["successor_rows_upper"])
        self.assertIsNone(result["successor_encoded_bytes_upper"])
        self.assertFalse(result["expanded_includes_measured"])

    def test_comment_guard_is_not_an_admission_claim(self):
        self.assertEqual(measure(b"$c wff $. $( valid EOF comment $)")["source_forms_in_file"], 1)
        for bad in (b"$( bad\x07 $)\n", b"$( open$(embedded $)\n",
                    b"$( close$)embedded $)\n", b"$c\x0bwff $.\n"):
            with self.assertRaises(ValueError):
                measure(bad)


if __name__ == "__main__":
    unittest.main()
