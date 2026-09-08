#!/bin/sh
set -eu

if [ "$#" -lt 1 ] || [ "$#" -gt 2 ]; then
    echo "usage: $0 <MM2 reader probe> [CeTTa MORK binary]" >&2
    exit 2
fi

reader_probe=$1
cetta_bin=${2-}
repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
artifact_dir=$repo_root/lean/mettapedia/artifacts/conformance/metamath_mm2_raw_unit
passed=0

if [ ! -x "$reader_probe" ]; then
    echo "FAIL: MM2 reader probe is not executable: $reader_probe" >&2
    exit 2
fi
if [ -n "$cetta_bin" ] && [ ! -x "$cetta_bin" ]; then
    echo "FAIL: CeTTa MORK binary is not executable: $cetta_bin" >&2
    exit 2
fi

for fixture in \
    test_stack_simple.mm2 \
    test_stack_fhyps.mm2 \
    test_dv_yz_required.mm2 \
    test22_typecode_mismatch_in_substitution.mm2 \
    test24_undefined_label_in_proof.mm2 \
    test26_wrong_conclusion_in_proof.mm2 \
    test27_disjoint_variable_constraint_violation.mm2
do
    source=$artifact_dir/$fixture
    if [ ! -f "$source" ]; then
        echo "FAIL: missing Metamath-generated MM2 fixture: $fixture" >&2
        exit 1
    fi
    if ! output=$("$reader_probe" --fused-only "$source" 2>&1); then
        echo "FAIL: generated MM2 reader rejected $fixture" >&2
        printf '%s\n' "$output" >&2
        exit 1
    fi
    case $output in
        *"PASS: MM2 authored reader parsed "*) ;;
        *)
            echo "FAIL: generated MM2 reader returned no parse receipt for $fixture" >&2
            printf '%s\n' "$output" >&2
            exit 1
            ;;
    esac
    passed=$((passed + 1))
done

echo "PASS: generated MM2 reader parsed $passed Metamath-to-MM2 conformance programs"

if [ -z "$cetta_bin" ]; then
    exit 0
fi

result_dir=$repo_root/lean/mettapedia/.lake/build/conformance/metamath_mm2_cogslt
mkdir -p "$result_dir"

count_tag() {
    tag=$1
    result_path=$2
    count=$(grep -c "^($tag " "$result_path" || true)
    printf '%s\n' "${count:-0}"
}

assert_count() {
    expected=$1
    tag=$2
    result_path=$3
    actual=$(count_tag "$tag" "$result_path")
    if [ "$actual" != "$expected" ]; then
        echo "FAIL: expected $expected $tag rows in $result_path, found $actual" >&2
        exit 1
    fi
}

assert_nat_tail() {
    tag=$1
    expected=$2
    result_path=$3
    if ! grep -Eq "^\\($tag .*\\(mm-nat $expected\\)\\)$" "$result_path"; then
        echo "FAIL: expected $tag to end at position $expected in $result_path" >&2
        exit 1
    fi
}

assert_quiescent_verifier() {
    result_path=$1
    assert_count 0 mm-accepted "$result_path"
    assert_count 0 mm-rejected "$result_path"
    assert_count 0 mm-proof-fault "$result_path"
    assert_count 0 mm-normal-control "$result_path"
    assert_count 0 mm-source-current "$result_path"
    assert_count 0 mm-source-action-running "$result_path"
    assert_count 0 mm-source-action-plan "$result_path"
    assert_count 0 mm-source-theorem-pending "$result_path"
    assert_count 0 mm-source-theorem-proof-context "$result_path"
}

run_and_check() {
    fixture=$1
    source_end=$2
    applied=$3
    verdict=$4
    reason=${5-}
    source=$artifact_dir/$fixture
    result_path=$result_dir/$fixture.result.mm2

    if ! "$cetta_bin" --lang mm2 --profile gslt "$source" > "$result_path"; then
        echo "FAIL: authored MM2 parser/executor rejected $fixture" >&2
        exit 1
    fi

    upstream_count=$("$cetta_bin" --count-only --lang mm2 "$source")
    gslt_count=$("$cetta_bin" --count-only --lang mm2 --profile gslt "$source")
    if [ "$upstream_count" != "$gslt_count" ]; then
        echo "FAIL: upstream MORK and authored GSLT final cardinalities differ for $fixture" >&2
        echo "upstream=$upstream_count gslt=$gslt_count" >&2
        exit 1
    fi

    assert_quiescent_verifier "$result_path"
    assert_count 1 mm-source-end "$result_path"
    assert_count "$applied" mm-source-statement-applied "$result_path"
    assert_nat_tail mm-source-end "$source_end" "$result_path"

    if [ "$verdict" = admitted ]; then
        assert_count 1 mm-source-theorem-admitted "$result_path"
        assert_count 0 mm-source-theorem-rejected "$result_path"
        assert_count 1 mm-source-control "$result_path"
        assert_nat_tail mm-source-control "$source_end" "$result_path"
    else
        assert_count 0 mm-source-theorem-admitted "$result_path"
        assert_count 1 mm-source-theorem-rejected "$result_path"
        assert_count 0 mm-source-control "$result_path"
        if ! grep -Eq "^\\(mm-source-theorem-rejected .* $reason " "$result_path"; then
            echo "FAIL: expected rejection reason $reason in $result_path" >&2
            exit 1
        fi
    fi
}

run_and_check test_stack_simple.mm2 8 8 admitted
run_and_check test_stack_fhyps.mm2 15 15 admitted
run_and_check test_dv_yz_required.mm2 15 15 admitted
run_and_check test22_typecode_mismatch_in_substitution.mm2 6 5 rejected typecode-mismatch
run_and_check test24_undefined_label_in_proof.mm2 5 4 rejected undefined-label
run_and_check test26_wrong_conclusion_in_proof.mm2 6 5 rejected wrong-conclusion
run_and_check test27_disjoint_variable_constraint_violation.mm2 8 7 rejected dv-same-variable

echo "PASS: generated MM2 parser and authored execution validated $passed Metamath verifier programs"
