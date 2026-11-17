"""The structural scan sees Lean code, not comments or strings.

An item has exactly one target theorem, closed by `by sorry` at the end of its one
namespace. A `sorry` inside a comment or string is not code, and a scan that
counted it would reject a valid item or miss a second target.
"""

import subprocess
from pathlib import Path

import pytest

from reuf2f.task import checks
from reuf2f.task.checks import (
    LEAN_CHECK,
    check_task_repo,
    check_item_scopes,
    lean_code,
    root_imports,
    target_scan,
)

TARGET = "theorem target : True := by sorry\n"


def test_nested_comments_are_masked():
    text = "/- outer /- theorem u : P := by sorry -/ sorry -/\ntheorem t : P := by sorry\n"
    code = lean_code(text)
    assert len(code) == len(text)
    assert code.count("\n") == text.count("\n")
    assert "theorem u" not in code
    assert code.count("sorry") == 1


def test_comment_markers_in_strings_are_masked():
    text = 'def s := "-- /- sorry \\" -/"\n-- sorry\n@[simp]\n'
    code = lean_code(text)
    assert "sorry" not in code
    assert "@[simp]" in code
    assert len(code) == len(text)


def test_a_terminal_line_comment_is_masked():
    assert lean_code("x -- hidden") == "x          "


def test_a_character_literal_is_masked():
    text = "def quote : Char := '\"'\n"
    assert len(lean_code(text)) == len(text)
    assert '"' not in lean_code(text)


def test_a_raw_string_is_masked():
    text = 'def s : String := r#"a "sorry" b"#\n'
    assert len(lean_code(text)) == len(text)
    assert "sorry" not in lean_code(text)


@pytest.mark.parametrize("text", ["/- unterminated", '"unterminated'])
def test_unterminated_input_is_refused(text):
    with pytest.raises(ValueError):
        lean_code(text)


def test_a_canonical_target_passes():
    code = lean_code("namespace X\ntheorem t : True := by\n  sorry\nend X\n")
    assert target_scan(code) == (["t"], 1, [])


@pytest.mark.parametrize(
    "code",
    [
        TARGET + "theorem extra : True := by trivial\n",
        "theorem t : True := by sorry; done",
        "lemma helper : True := by sorry\n" + TARGET,
        "def helper : Nat := by sorry\n",
        "theorem t : True := sorry\n",
    ],
    ids=["not-last", "code-after-sorry", "setup-sorry", "sorry-in-def", "term-sorry"],
)
def test_a_noncanonical_target_is_refused(code):
    assert target_scan(code)[2]


@pytest.mark.parametrize(
    ("text", "name"),
    [
        ("@[simp] @[reducible] theorem «target» : True := by sorry\n", "«target»"),
        ("@[simp,\n  reducible] theorem t : True := by sorry\n", "t"),
    ],
)
def test_the_target_is_the_theorem_proved_by_sorry(text, name):
    assert target_scan(lean_code(text)) == ([name], 1, [])


def test_a_proved_setup_lemma_passes():
    assert not target_scan("lemma helper : 2 = (2 : Nat) := by rfl\n" + TARGET)[2]


@pytest.mark.parametrize("name", ["X'", "«Object API»"])
def test_the_target_may_close_any_namespace_name(name):
    code = lean_code(f"namespace {name}\n{TARGET}end {name}\n")
    assert not target_scan(code)[2]


def test_the_lean_checks_ship_beside_the_structural_scan():
    assert LEAN_CHECK.is_file()
    assert "import reuF2F" in LEAN_CHECK.read_text()


def test_a_failing_lean_check_is_a_problem(monkeypatch):
    root = Path(__file__).resolve().parents[1]
    calls = []

    def lean(command, **kwargs):
        calls.append((command, kwargs["cwd"]))
        return subprocess.CompletedProcess(command, 1, "error: target uses sorryAx\n", "")

    monkeypatch.setattr(checks.subprocess, "run", lean)
    [problem] = check_task_repo(root)
    assert calls == [(["lake", "env", "lean", str(LEAN_CHECK)], root / "lean")]
    assert problem.where == "check.lean" and problem.severity == "error"
    assert "target uses sorryAx" in problem.message


def test_roots_use_one_plain_import_per_line():
    assert root_imports("import reuF2F.x\nimport reuF2F.y\n") == [
        "reuF2F.x",
        "reuF2F.y",
    ]
    for text in [
        "import reuF2F.x reuF2F.y",
        "import reuF2F.x -- comment",
        "import\treuF2F.x",
    ]:
        with pytest.raises(ValueError):
            root_imports(text)


@pytest.mark.parametrize(
    ("source", "invalid"),
    [
        pytest.param(
            "noncomputable section\nnamespace X\nend X\n",
            False,
            id="filewide_noncomputable_section",
        ),
        pytest.param(
            "namespace X\nend X\nnamespace X\nend X\n",
            True,
            id="reopened_item_namespace",
        ),
        pytest.param(
            "section\nnamespace X\nend X\nend\n", True, id="anonymous_section"
        ),
        pytest.param("namespace X\nend\n", True, id="anonymous_end"),
        pytest.param(
            "noncomputable section\nnamespace X\nsection Setup\nnamespace Object\nend Object\nend Setup\nend X\n",
            False,
            id="named_setup_and_source_object_namespace",
        ),
        pytest.param(
            "namespace X\nnoncomputable section\nend\nend X\n",
            True,
            id="nested_noncomputable_section",
        ),
        pytest.param("namespace X\n", True, id="unclosed_named_scope"),
        pytest.param("namespace X\nend Y\n", True, id="mismatched_named_end"),
        pytest.param(
            "/- namespace Y\nend -/\nnamespace X\nend X\n",
            False,
            id="comment_commands_do_not_count",
        ),
        pytest.param("namespace X'\nend X'\n", False, id="primed_namespace"),
        pytest.param(
            "namespace «Object API»\nend «Object API»\n", False, id="escaped_namespace"
        ),
        pytest.param(
            "namespace «X»\nend X\n", False, id="escaped_and_bare_names_match"
        ),
        pytest.param(
            "namespace X!?\nend X!?\n", False, id="punctuation_namespace_suffixes"
        ),
        pytest.param(
            "namespace X\nnamespace\n  Object\nend\n  Object\nend X\n",
            False,
            id="multiline_scope_names",
        ),
        pytest.param(
            "namespace X\nsection\n  Setup\nend Setup\nend X\n",
            False,
            id="multiline_named_section",
        ),
        pytest.param(
            "namespace X\nnamespace Object'\nend Wrong'\nend X\n",
            True,
            id="mismatched_primed_namespace",
        ),
        pytest.param(
            "namespace «X.Y»\nend X.Y\n",
            True,
            id="escaped_dot_is_not_a_namespace_separator",
        ),
        pytest.param(
            "namespace «X /- -- API»\nend «X /- -- API»\n",
            False,
            id="comment_markers_in_identifier_escape",
        ),
    ],
)
def test_item_scope_syntax(source, invalid):
    assert bool(check_item_scopes(lean_code(source))) == invalid
