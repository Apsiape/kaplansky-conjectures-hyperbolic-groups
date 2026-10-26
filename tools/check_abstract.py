"""Check that every surface carrying the abstract carries the same abstract.

The source of truth is the abstract environment of paper/main.tex. The other surfaces are

* arxiv/abstract.txt (a local build product, git-ignored): the paper's TeX with the macro \\F expanded
  to \\mathbb{F}, which is the form arXiv accepts;
* the "description" field of .zenodo.json: the same text serialized as HTML (one paragraph, variables in
  <i>, subscripts in <sub>, the symbols written as Unicode characters);
* the "abstract" field of CITATION.cff, if there is one (there is none at present).

The README carries a shorter summary, labelled as such; it is not an abstract and is not checked.

Each surface is compared in two ways:
1. literally, against the serialization that this script produces from the paper; and
2. after normalization to plain text (markup and math delimiters removed, symbols mapped to one spelling,
   spacing around operators and commas removed), so that a mismatch is reported in readable form.
The script also checks that the arXiv abstract is within arXiv's limit of 1920 characters.

Usage:
    python tools/check_abstract.py           # check; exit status 1 on any mismatch
    python tools/check_abstract.py --write   # rewrite arxiv/abstract.txt and the Zenodo description from the paper
"""
from html import unescape
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "paper" / "main.tex"
ARXIV = ROOT / "arxiv" / "abstract.txt"
ZENODO = ROOT / ".zenodo.json"
CITATION = ROOT / "CITATION.cff"
ARXIV_LIMIT = 1920

MACROS = {r"\F": r"\mathbb{F}"}  # macros of the paper that occur in the abstract


def paper_abstract() -> str:
    tex = PAPER.read_text(encoding="utf-8")
    match = re.search(r"\\begin\{abstract\}(.*?)\\end\{abstract\}", tex, re.S)
    if not match:
        raise SystemExit("no abstract environment in paper/main.tex")
    return " ".join(match.group(1).split())


def expand_macros(tex: str) -> str:
    for macro, expansion in MACROS.items():
        tex = re.sub(re.escape(macro) + r"(?![A-Za-z])", lambda _: expansion, tex)
    return tex


def split_math(tex: str):
    """Yield (is_math, text) pieces of a TeX string with $...$ math."""
    parts = tex.split("$")
    if len(parts) % 2 == 0:
        raise SystemExit("unbalanced $ in the abstract")
    for i, part in enumerate(parts):
        yield i % 2 == 1, part


MATH_TOKENS = [
    (r"\\mathbb\{F\}", "\U0001D53D"),  # double-struck F
    (r"\\neq", " \u2260 "),
    (r"\\in", " \u2208 "),
    (r"=", " = "),
    (r"-", " \u2212 "),
    (r",", ", "),
]


def math_to_html(math: str) -> str:
    out, i = [], 0
    while i < len(math):
        if math[i].isspace():
            i += 1
            continue
        for pattern, html in MATH_TOKENS:
            m = re.match(pattern + (r"(?![A-Za-z])" if pattern.startswith("\\\\") else ""), math[i:])
            if m:
                out.append(html)
                i += m.end()
                break
        else:
            m = re.match(r"_(\{[^}]*\}|.)", math[i:])
            if m:
                sub = m.group(1).strip("{}")
                out.append("<sub>" + math_to_html(sub) + "</sub>")
                i += m.end()
                continue
            m = re.match(r"[A-Za-z]+", math[i:])
            if m:
                out.append("<i>" + m.group(0) + "</i>")
                i += m.end()
                continue
            if math[i] == "\\":
                raise SystemExit(f"unknown TeX command in math: {math[i:i + 20]!r}")
            out.append(math[i])
            i += 1
    return " ".join("".join(out).split())


def prose_to_html(text: str) -> str:
    if "\\" in text or "{" in text or "}" in text:
        raise SystemExit(f"TeX command in the prose of the abstract; extend this script: {text!r}")
    text = text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    return text.replace("~", " ").replace("---", "\u2014").replace("--", "\u2013")


def tex_to_html(tex: str) -> str:
    pieces = [math_to_html(t) if is_math else prose_to_html(t) for is_math, t in split_math(expand_macros(tex))]
    return "<p>" + "".join(pieces) + "</p>"


def normalize_tex(tex: str) -> str:
    tex = expand_macros(tex)
    for pattern, plain in [(r"\\neq(?![A-Za-z])", "\u2260"), (r"\\in(?![A-Za-z])", "\u2208"),
                           (r"\\mathbb\{F\}", "F")]:
        tex = re.sub(pattern, plain, tex)
    unknown = re.search(r".{0,20}\\[A-Za-z]+.{0,20}", tex)
    if unknown:
        raise SystemExit("unknown TeX command in the abstract; extend this script: " + repr(unknown.group(0)))
    return finish(tex.replace("$", "").replace("~", " "))


def normalize_html(html: str) -> str:
    html = html.strip()
    if not (html.startswith("<p>") and html.endswith("</p>")) or html.count("<p>") != 1:
        raise SystemExit("the Zenodo description should be a single <p> paragraph")
    html = html.replace("<sub>", "_")
    html = re.sub(r"<[^>]+>", "", html)
    html = unescape(html).replace("\U0001D53D", "F").replace("\u2212", "-").replace("\u00a0", " ")
    return finish(html)


def finish(text: str) -> str:
    text = " ".join(text.split())
    return re.sub(r"\s*([=\u2260\u2208,\-])\s*", r"\1", text)


def first_difference(a: str, b: str) -> str:
    i = next((k for k, (x, y) in enumerate(zip(a, b)) if x != y), min(len(a), len(b)))
    return f"at character {i}:\n    expected ...{a[max(0, i - 40):i + 40]!r}\n    found    ...{b[max(0, i - 40):i + 40]!r}"


def main() -> int:
    sys.stdout.reconfigure(errors="backslashreplace")
    write = "--write" in sys.argv[1:]
    tex = paper_abstract()
    arxiv_expected = expand_macros(tex)
    zenodo_expected = tex_to_html(tex)
    reference = normalize_tex(tex)
    failures = []

    if write:
        ARXIV.parent.mkdir(exist_ok=True)
        ARXIV.write_text(arxiv_expected + "\n", encoding="utf-8", newline="\n")
        data = json.loads(ZENODO.read_text(encoding="utf-8"))
        data["description"] = zenodo_expected
        ZENODO.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")
        print("wrote arxiv/abstract.txt and the description in .zenodo.json")

    print(f"paper abstract: {len(arxiv_expected)} characters after expanding macros "
          f"({len(normalize_tex(tex))} as normalized plain text); arXiv limit {ARXIV_LIMIT}")
    if len(arxiv_expected) > ARXIV_LIMIT:
        failures.append(f"the abstract has {len(arxiv_expected)} characters, over arXiv's limit of {ARXIV_LIMIT}")

    if ARXIV.exists():
        arxiv = ARXIV.read_text(encoding="utf-8").rstrip("\n")
        if arxiv != arxiv_expected:
            failures.append("arxiv/abstract.txt differs from the paper " + first_difference(arxiv_expected, arxiv))
        elif normalize_tex(arxiv) != reference:
            failures.append("arxiv/abstract.txt: normalized text differs")
        else:
            print("arxiv/abstract.txt: identical to the paper (with \\F expanded)")
    else:
        print("arxiv/abstract.txt: not present (git-ignored build product); run with --write to create it")

    description = json.loads(ZENODO.read_text(encoding="utf-8"))["description"]
    if description != zenodo_expected:
        failures.append(".zenodo.json description differs from the HTML serialization of the paper's abstract "
                        + first_difference(zenodo_expected, description))
    if normalize_html(description) != reference:
        failures.append(".zenodo.json description: normalized text differs from the paper "
                        + first_difference(reference, normalize_html(description)))
    if description == zenodo_expected and normalize_html(description) == reference:
        print(".zenodo.json: identical to the paper (HTML serialization)")

    cff = CITATION.read_text(encoding="utf-8")
    if re.search(r"^abstract:", cff, re.M):
        failures.append("CITATION.cff has an abstract field; add it to this check or remove it")
    else:
        print("CITATION.cff: no abstract field")

    for failure in failures:
        print("MISMATCH: " + failure)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
