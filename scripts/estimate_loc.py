#!/usr/bin/env python3
"""Estimate lines of *trusted specification*, *auxiliary specification* (split
into definitions and lemma statements), and *proof* for the worked examples in
this F* development (Secure Message Delivery and NSL Mutual Authentication).

F* mixes specification and proof in the same source tree, so the split is
necessarily an estimate.  We use the following heuristic, applied at the
granularity of top-level declarations.

Boilerplate
-----------
Comments (``// ...``, ``/// ...`` doc comments, and ``(* ... *)`` blocks), blank
lines, attributes (``[@@ ...]``), and module-level directives (``module``,
``open``, ``#push-options``, ``#set-options``, ``#pop-options``,
``#restart-solver``) are *boilerplate*: counted separately and excluded from the
spec/proof totals.

The four buckets
----------------
**Trusted specification** is the part of the development a reader must audit for
the theorem to mean anything: the term algebra, the adversary's derivation
rules, the protocol/ideal-functionality/simulator transition relations, the
definitions of static equivalence and T-equivalence, the statement of each
example's top-level theorem, and every *admitted* declaration.  If any of these
is wrong, the proved theorem is the wrong theorem.

**Auxiliary definitions** are the non-trusted definitions: inductive invariants,
the bisimulation relation and its witnesses, the substitution/bijection
machinery, and the observational-bisimulation proof technique itself.

**Auxiliary lemmas** are the *statements* of all the intermediate lemmas.

The two auxiliary buckets are convenience: they are checked by F*, so an error
in them shows up as a failed proof, not as an unsound theorem.  Which side of
the spec/proof line they belong on is a judgement call — auxiliary definitions
read as specification, auxiliary lemma statements read more like proof effort —
so they are reported separately and can be added to either total.

**Proof** is the body of every lemma that actually has one.

Classification rules
--------------------
Which modules (and, for mixed modules, which declarations) are trusted is
configured explicitly in ``TRUSTED`` below — that list *is* the trusted
computing base of this development, so it is spelled out rather than inferred.
Given that list:

  * A top-level ``let``/``let rec`` is a **lemma** if either
      - its own signature (the text before the body ``=``) mentions ``Lemma``
        or ``squash``, or
      - a matching ``val NAME : ... Lemma ...`` appears in this module or in the
        module's ``.fsti`` interface (lemmas whose statement lives in the
        interface but whose proof lives in the ``.fst``).
    A ``val NAME : ... Lemma ...`` is itself a lemma with an empty body.

  * A declaration is **admitted** if its body is ``admit ()`` / ``assume`` /
    ``magic ()`` — here or, for a ``val``, in the sibling implementation.  An
    admitted declaration is an *axiom*, not a proved fact, so its statement
    counts as **trusted specification**: the four admitted declarations in this
    development are the two metatheory theorems of ``ObservationalBisimulation``
    (proved in the companion Lean development) and ``FStar.PartialMap.Ext.map``
    / ``sel_map``.

  * A lemma's *body* is **proof** — including an admitted lemma's
    ``admit ()`` stub, which is a line or two and not worth a special case.

  * A non-admitted lemma's *statement* is an **auxiliary lemma** — unless the
    lemma is explicitly named in ``TRUSTED`` (the two top-level theorems,
    ``smd_t_equivalence`` and ``ma_t_equivalence``, are: their statements say
    what was actually proved), in which case it is **trusted specification**.

  * Every other declaration — ``type``/``noeq type`` datatypes, records, ``val``
    signatures, ``class``/``instance`` definitions, and ordinary (non-lemma)
    ``let`` definitions such as the protocol transition relations and the
    bisimulation relation — counts entirely as specification, **trusted** if the
    declaration is covered by ``TRUSTED`` and an **auxiliary definition**
    otherwise.

Every source line lands in exactly one of the five buckets, so
``trusted + aux-def + aux-lemma + proof + boilerplate == total`` for every file.

This is a heuristic. It will misclassify the occasional declaration (e.g. a
non-lemma ``let`` whose body is really proof-by-construction), but across a
codebase this size the aggregate is a faithful estimate.
"""

from __future__ import annotations

import argparse
import os
import re
from dataclasses import dataclass

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# ---------------------------------------------------------------------------
# Per-example configuration.  Edit these to change what counts as each example.
# ---------------------------------------------------------------------------


@dataclass
class Example:
    key: str                 # short id used on the command line
    title: str               # human-readable name
    example_dir: str         # directory of example-specific modules
    specific_core: list[str] # root modules used *only* by this example
    core_title: str          # label for the example-specific adversary core


EXAMPLES = {
    "smd": Example(
        key="smd",
        title="Secure Message Delivery (symmetric encryption)",
        example_dir=os.path.join(REPO, "examples", "secure_message_delivery"),
        # Root-level modules used only by SMD (symmetric encryption).
        specific_core=["SencTerms", "AdversarySenc"],
        core_title="Senc adversary core",
    ),
    "ma": Example(
        key="ma",
        title="NSL Mutual Authentication (asymmetric encryption)",
        example_dir=os.path.join(REPO, "examples", "nsl_mutual_authentication"),
        # Root-level modules used only by NSL MA (asymmetric encryption).
        specific_core=["AencTerms", "AdversaryAenc"],
        core_title="Aenc adversary core",
    ),
}

# Core infrastructure shared by both examples.
SHARED_CORE = [
    "SymbolicTypes",
    "Adversary",
    "StaticEquivalence",
    "Protocol",
    "TestedSystem",
    "TestEquivalence",
    "ObservationalBisimulation",
]

# Generic helper libraries shared across the development.
SHARED_HELPERS_DIR = os.path.join(REPO, "helpers")


# ---------------------------------------------------------------------------
# Trusted computing base.
#
# Keys are module base paths relative to the repository root, without an
# extension; a key covers both the ``.fsti`` and the ``.fst``.  The value is
# either ``ALL`` (every non-lemma declaration in the module is trusted) or an
# explicit set of top-level declaration names.  Modules absent from this table
# are auxiliary in their entirety.
#
# Naming a *lemma* here (only the two top-level theorems are) makes its
# statement trusted; its body still counts as proof.
# ---------------------------------------------------------------------------

ALL = "*"

TRUSTED: dict[str, object] = {
    # -- Shared framework: the model and the security definition -------------
    # Terms, knowledge, worlds; the adversary interface; the RLTS model; the
    # tested system (protocol || adversary); and T-equivalence itself.
    "SymbolicTypes": ALL,
    "Adversary": ALL,
    "Protocol": ALL,
    "TestedSystem": ALL,
    "TestEquivalence": ALL,
    # StaticEquivalence also holds the `bijective_correspondence_*` machinery,
    # which is a proof device for establishing static equivalence, not part of
    # its definition.
    "StaticEquivalence": {"indistinguishable'", "statically_equivalent"},
    # `ObservationalBisimulation` states a proof technique (paper §4) rather
    # than the security property, but its two theorems are *admitted* here and
    # proved in the companion Lean development.  Auditing that the F* axioms say
    # what Lean proved means auditing the definitions they quantify over --
    # `obs_bisim_up_to_partitions`, `right_movable`, and everything feeding
    # them, which is the whole module.
    "ObservationalBisimulation": ALL,

    # -- Shared helpers ------------------------------------------------------
    # Bag is the multiset used by the trusted protocol state, and `partition`
    # is the equivalence-class structure the two admitted metatheory theorems
    # quantify over; the lemmas of both are picked up as auxiliary
    # automatically.  The remaining helpers (FStar.Set.Properties,
    # FStar.Bijection.Ext, FStar.PartialMap.Ext) exist only to support the
    # proofs -- except PartialMap.Ext's two admitted declarations, which the
    # admit rule picks up on its own.
    "helpers/Bag": ALL,
    "helpers/Partition": ALL,

    # -- Senc adversary core (SMD) -------------------------------------------
    "SencTerms": ALL,
    "AdversarySenc": {
        "derivation", "derive", "derivable", "indistinguishable",
        "adversary_senc",
        # `in_term` is a hypothesis of `smd_t_equivalence` (the initial
        # knowledge contains no ciphertext under the secret key), so it is part
        # of what the theorem statement means.
        "in_term",
    },

    # -- Aenc adversary core (NSL MA) ----------------------------------------
    "AencTerms": ALL,
    "AdversaryAenc": {
        "derivation", "derive", "derivable", "indistinguishable",
        "adversary_aenc",
    },

    # -- SMD case study ------------------------------------------------------
    "examples/secure_message_delivery/SMD.Types": ALL,
    "examples/secure_message_delivery/SMD.Adversary": ALL,
    "examples/secure_message_delivery/SMD.Implementation": ALL,
    "examples/secure_message_delivery/SMD.Ideal": ALL,
    "examples/secure_message_delivery/SMD.TestedProtocols": ALL,
    "examples/secure_message_delivery/SMD.ObservationalBisimulation.Proof": {
        "smd_t_equivalence",
    },

    # -- NSL MA case study ---------------------------------------------------
    # MA.Types mixes the protocol's vocabulary (effects, roles, label ids,
    # input terms, the nonces of the initial knowledge) with `aenc_subterm` /
    # `shallow_aenc` / `Set` scaffolding used only by the proofs.
    "examples/nsl_mutual_authentication/MA.Types": {
        "ma_effect", "role", "complementary_role", "ma_label_id",
        "ma_io_input_term", "ma_net_input_term", "ma_auth_input_payload_term",
        "ma_auth_input_term", "ma_authenticated_term",
        "ma_term_nonces", "ma_term_list_nonces", "ma_knowledge_nonces",
    },
    "examples/nsl_mutual_authentication/MA.Adversary": {"adv"},
    # `ma_key_directory_injective` happens to live among the ideal-world
    # invariants, but it is a hypothesis of `ma_t_equivalence`, not an invariant.
    "examples/nsl_mutual_authentication/MA.IdealInvariants": {
        "ma_key_directory_injective",
    },
    "examples/nsl_mutual_authentication/MA.NSL": ALL,
    "examples/nsl_mutual_authentication/MA.Ideal": ALL,
    "examples/nsl_mutual_authentication/MA.TestedProtocols": ALL,
    "examples/nsl_mutual_authentication/MA.ObservationalBisimulation.Proof": {
        "ma_t_equivalence",
    },
}


def module_base(path: str) -> str:
    """Repo-relative module path without its .fst/.fsti extension."""
    rel = os.path.relpath(path, REPO)
    return rel[:-5] if rel.endswith(".fsti") else rel[:-4]


def trusted_config_for(path: str) -> str | frozenset[str] | None:
    """The ``TRUSTED`` entry covering `path`, or None if the module is wholly
    auxiliary."""
    cfg = TRUSTED.get(module_base(path))
    if cfg is None or cfg is ALL:
        return cfg
    return frozenset(cfg)  # type: ignore[arg-type]


def configured_names(cfg: object) -> frozenset[str]:
    """The declaration names a ``TRUSTED`` entry mentions, for the stale check.
    ``ALL`` mentions none."""
    if cfg is None or cfg is ALL:
        return frozenset()
    return frozenset(cfg)  # type: ignore[arg-type]


# Declaration names seen per module (across .fsti and .fst), so that a stale
# entry in `TRUSTED` — a declaration that was renamed or removed — is reported
# rather than silently counted as auxiliary.
_seen_decl_names: dict[str, set[str]] = {}


# ---------------------------------------------------------------------------
# Tokenization / comment stripping
# ---------------------------------------------------------------------------

DIRECTIVE_RE = re.compile(
    r"^\s*(module\s+\w|open\s|friend\s|include\s|"
    r"#push-options|#pop-options|#set-options|#reset-options|#restart-solver)"
)

# Keyword that begins a top-level declaration (column 0, possibly preceded by
# attributes/qualifiers which we strip first).
DECL_KEYWORDS = (
    "val", "let", "type", "and", "class", "instance",
    "assume", "effect", "new_effect", "exception",
)

# A declaration is a *lemma* when its result type is proof-irrelevant: either
# the `Lemma` effect or a `squash` of the property it establishes (the shape the
# `valid_transitions` obligations use).
LEMMA_RE = re.compile(r"\b(Lemma|squash)\b")

# A declaration whose body is one of these is admitted: F* takes it on faith, so
# it is an axiom of this development rather than a result proved by it.
ADMIT_RE = re.compile(r"\b(admit|magic|assume|admit_smt_pat)\b")

QUALIFIER_RE = re.compile(
    r"^(private\s+|abstract\s+|noeq\s+|unopteq\s+|unfold\s+|inline_for_extraction\s+|"
    r"rec\s+|total\s+|noextract\s+|irreducible\s+|assume\s+)+"
)


def strip_comments(text: str) -> str:
    """Remove (* ... *) block comments (handles nesting) and // line comments.

    Doc comments (///) are treated as line comments. We blank the comment
    characters out rather than deleting lines so line numbering is preserved.
    """
    out = []
    i = 0
    n = len(text)
    depth = 0  # block-comment nesting depth
    while i < n:
        two = text[i:i + 2]
        if depth > 0:
            if two == "(*":
                depth += 1
                i += 2
                continue
            if two == "*)":
                depth -= 1
                i += 2
                continue
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
            continue
        # not currently in a block comment
        if two == "(*":
            depth += 1
            i += 2
            continue
        if two == "//":
            # line comment: blank to end of line
            while i < n and text[i] != "\n":
                i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def is_blank(line: str) -> bool:
    return line.strip() == ""


def is_boilerplate_line(line: str) -> bool:
    """A line that is neither specification nor proof: blank, a module-level
    directive (``module``/``open``/``#push-options``/…), or an attribute
    (``[@@ ...]``).  Such a line is boilerplate *even when it falls inside a
    declaration's line range* (e.g. a ``#push-options`` sitting between two
    lemmas, or an attribute attached to the following decl)."""
    if is_blank(line):
        return True
    if DIRECTIVE_RE.match(line):
        return True
    if line.lstrip().startswith("[@"):
        return True
    return False


# ---------------------------------------------------------------------------
# Declaration parsing
# ---------------------------------------------------------------------------

@dataclass
class Decl:
    keyword: str          # 'val', 'let', 'type', ...
    name: str | None
    start: int            # line index (0-based), inclusive
    end: int              # line index, exclusive
    sig_lines: int        # lines belonging to the signature/statement
    body_lines: int       # lines belonging to the body (0 for val/type)
    is_lemma: bool = False


def declaration_starts(lines: list[str]) -> list[int]:
    """Return indices of lines that begin a top-level declaration.

    A top-level declaration starts at column 0 (no leading whitespace) with a
    declaration keyword, after stripping qualifiers/attributes.
    """
    starts = []
    for idx, raw in enumerate(lines):
        if raw[:1] in (" ", "\t"):
            continue  # indented => continuation of previous declaration
        line = raw
        # strip leading attribute(s) like [@@ ... ]
        if line.lstrip().startswith("[@"):
            # attribute line; the decl keyword is on a later line, skip
            continue
        stripped = QUALIFIER_RE.sub("", line)
        m = re.match(r"^(\w+)", stripped)
        if m and m.group(1) in DECL_KEYWORDS:
            starts.append(idx)
    return starts


def find_body_split(block_text: str) -> int | None:
    """Find the character offset of the top-level body '=' in a let block.

    Returns None if no top-level '=' is found (e.g. a `val`, or a lemma whose
    body lives in another file). Skips '=' that is part of ==, <=, >=, =!=,
    :=, ->, <>, and skips anything inside (), [], {}.
    """
    depth = 0
    i = 0
    n = len(block_text)
    while i < n:
        c = block_text[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == "=" and depth == 0:
            prev = block_text[i - 1] if i > 0 else ""
            nxt = block_text[i + 1] if i + 1 < n else ""
            # not part of a multi-char operator
            if prev in "<>=!:+-*/|&^~" or nxt in "=<>":
                i += 1
                continue
            return i
        i += 1
    return None


def parse_module(lines: list[str], lemma_names_from_fsti: set[str]) -> list[Decl]:
    starts = declaration_starts(lines)
    decls: list[Decl] = []
    bounds = starts + [len(lines)]
    for j, start in enumerate(starts):
        end = bounds[j + 1]
        block_lines = lines[start:end]
        raw = lines[start]
        stripped = QUALIFIER_RE.sub("", raw)
        m = re.match(r"^(\w+)", stripped)
        keyword = m.group(1)
        # extract a name token (best-effort)
        nm = re.match(r"^\w+\s+(?:rec\s+)?\(?([A-Za-z_][A-Za-z0-9_'.]*)", stripped)
        name = nm.group(1) if nm else None

        block_text = "".join(block_lines)
        total = end - start

        is_lemma = False
        sig_lines = total
        body_lines = 0

        if keyword == "val":
            # A `val NAME : ... Lemma ...` is a lemma statement with no body
            # here; the proof (if any) lives in the sibling .fst.
            is_lemma = bool(LEMMA_RE.search(block_text))
        elif keyword == "let":
            split = find_body_split(block_text)
            sig_text = block_text[:split] if split is not None else block_text
            # lemma if its own signature mentions Lemma, or the fsti declares it so
            if LEMMA_RE.search(sig_text) or (name in lemma_names_from_fsti):
                is_lemma = True
            if split is not None:
                lines_before = block_text.count("\n", 0, split)
                # Is there body text after the '=' on the *same* line?
                nl = block_text.find("\n", split)
                tail = block_text[split + 1: nl if nl != -1 else len(block_text)]
                if tail.strip():
                    # e.g. `let f x = ()` -- the split line carries the body,
                    # so it counts toward the body region, not the signature.
                    sig_lines = lines_before
                else:
                    # `=` ends the line; the body starts on the next line.
                    sig_lines = lines_before + 1
                body_lines = total - sig_lines
            else:
                sig_lines = total
                body_lines = 0
        # type / class / instance / etc: all signature/spec.

        decls.append(Decl(keyword, name, start, end, sig_lines, body_lines, is_lemma))
    return decls


def lemma_names_in_fsti(text: str) -> set[str]:
    """Names of `val NAME : ... Lemma ...` (or `... squash ...`) declarations
    in an interface."""
    names: set[str] = set()
    lines = text.splitlines(keepends=True)
    starts = declaration_starts(lines)
    bounds = starts + [len(lines)]
    for j, start in enumerate(starts):
        raw = lines[start]
        stripped = QUALIFIER_RE.sub("", raw)
        if not stripped.startswith("val"):
            continue
        block = "".join(lines[start:bounds[j + 1]])
        nm = re.match(r"^val\s+\(?([A-Za-z_][A-Za-z0-9_'.]*)", stripped)
        if nm and LEMMA_RE.search(block):
            names.add(nm.group(1))
    return names


def admitted_names_in(text: str) -> set[str]:
    """Names of top-level declarations in `text` whose body is admitted.

    Comments are already stripped by the caller, so a prose mention of "admit"
    in a doc comment does not count -- only an actual ``admit ()`` in the body.
    """
    names: set[str] = set()
    lines = text.splitlines(keepends=True)
    for d in parse_module(lines, set()):
        if d.name is None or d.body_lines == 0:
            continue
        body = "".join(lines[d.start + d.sig_lines: d.end])
        if ADMIT_RE.search(body):
            names.add(d.name)
    return names


# ---------------------------------------------------------------------------
# Per-file counting
# ---------------------------------------------------------------------------

@dataclass
class Counts:
    trusted: int = 0       # trusted spec: the model, theorem statements, axioms
    aux_def: int = 0       # auxiliary definitions: invariants, relations, witnesses
    aux_lemma: int = 0     # auxiliary lemma statements
    proof: int = 0         # lemma bodies
    boilerplate: int = 0   # directives, comments-only, blank
    total: int = 0

    @property
    def aux(self) -> int:
        return self.aux_def + self.aux_lemma

    @property
    def spec(self) -> int:
        return self.trusted + self.aux

    def __iadd__(self, other: "Counts") -> "Counts":
        self.trusted += other.trusted
        self.aux_def += other.aux_def
        self.aux_lemma += other.aux_lemma
        self.proof += other.proof
        self.boilerplate += other.boilerplate
        self.total += other.total
        return self


# Admitted declarations found while counting, as "module: name" -- reported at
# the end, since they are the axioms the whole development rests on.
_admitted_found: set[str] = set()


def count_file(path: str, lemma_names_from_fsti: set[str]) -> Counts:
    with open(path, "r", encoding="utf-8") as f:
        original = f.read()
    stripped = strip_comments(original)
    src_lines = stripped.splitlines(keepends=True)
    if not src_lines:
        return Counts(total=0)

    c = Counts(total=len(src_lines))
    # A lemma's statement may live in a `val`: in the sibling .fsti, or in this
    # very file (`val NAME : ... Lemma ...` above `let NAME = <proof>`).
    own_lemma_names = lemma_names_in_fsti(stripped)
    decls = parse_module(src_lines, lemma_names_from_fsti | own_lemma_names)

    # A `val` in an interface is admitted when the implementation admits it.
    admitted = admitted_names_in(stripped) | sibling_admitted_names(path)

    trusted_cfg = trusted_config_for(path)
    _seen_decl_names.setdefault(module_base(path), set()).update(
        d.name for d in decls if d.name is not None
    )

    # mark which lines belong to declarations
    covered = [False] * len(src_lines)

    for d in decls:
        # An admitted declaration is an axiom: F* never checks it, so its
        # statement is trusted wherever it lives.
        is_admitted = d.name is not None and d.name in admitted
        if is_admitted:
            _admitted_found.add(f"{module_base(path)}.{d.name}")
            is_trusted = True
        elif trusted_cfg is None:
            is_trusted = False
        elif trusted_cfg is ALL:
            # A lemma is a derived fact, never part of the trusted base — even
            # in a module whose definitions all are.
            is_trusted = not d.is_lemma
        else:
            is_trusted = d.name is not None and d.name in trusted_cfg

        def bucket(is_body: bool) -> str:
            if d.is_lemma and is_body:
                # A lemma body is proof even when the statement is trusted: a
                # top-level theorem, or an admitted lemma's `admit ()` stub.
                return "proof"
            if is_trusted:
                return "trusted"
            return "aux_lemma" if d.is_lemma else "aux_def"

        for i in range(d.start, d.end):
            covered[i] = True
        sig_end = d.start + d.sig_lines
        # Signature region: statement/specification.  Body region: proof for a
        # lemma, specification for a plain definition.  Directives (e.g. a
        # #push-options around a proof), attributes, and blanks are boilerplate
        # wherever they sit.
        for i in range(d.start, d.end):
            if is_boilerplate_line(src_lines[i]):
                c.boilerplate += 1
            else:
                setattr(c, b := bucket(i >= sig_end), getattr(c, b) + 1)

    # lines outside any declaration: module header, opens, comment-only, blanks
    for i in range(len(src_lines)):
        if not covered[i]:
            c.boilerplate += 1

    # Every source line now lands in exactly one bucket, so
    # trusted + aux_def + aux_lemma + proof + boilerplate == total.
    assert c.spec + c.proof + c.boilerplate == c.total, path
    return c


# ---------------------------------------------------------------------------
# File-group resolution
# ---------------------------------------------------------------------------

def module_files(base: str) -> list[str]:
    """Return existing .fsti/.fst paths for a root-level module base name."""
    out = []
    for ext in (".fsti", ".fst"):
        p = os.path.join(REPO, base + ext)
        if os.path.exists(p):
            out.append(p)
    return out


def dir_fstar_files(d: str) -> list[str]:
    out = []
    for fn in sorted(os.listdir(d)):
        if fn.endswith(".fst") or fn.endswith(".fsti"):
            out.append(os.path.join(d, fn))
    return out


def fsti_lemma_set_for(path: str) -> set[str]:
    """If `path` is a .fst, read the sibling .fsti for lemma val-names."""
    if not path.endswith(".fst"):
        return set()
    fsti = path[:-4] + ".fsti"
    if not os.path.exists(fsti):
        return set()
    with open(fsti, "r", encoding="utf-8") as f:
        return lemma_names_in_fsti(strip_comments(f.read()))


def sibling_admitted_names(path: str) -> set[str]:
    """If `path` is a .fsti, the names its sibling .fst admits.

    A `val` in an interface carries no body, so whether it is an axiom or a
    proved result is only visible in the implementation."""
    if not path.endswith(".fsti"):
        return set()
    fst = path[:-1]
    if not os.path.exists(fst):
        return set()
    with open(fst, "r", encoding="utf-8") as f:
        return admitted_names_in(strip_comments(f.read()))


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

NAMEW = 58            # width of the leading name column
W = NAMEW + 6 * 9     # per-file table width
SUMW = NAMEW + 8 * 9  # summary table width


def _row(name: str, c: Counts) -> str:
    return (f"{name[:NAMEW]:{NAMEW}} {c.trusted:>8} {c.aux_def:>8} "
            f"{c.aux_lemma:>8} {c.proof:>8} {c.boilerplate:>8} {c.total:>8}")


def report_group(title: str, files: list[str], root: str = REPO) -> Counts:
    """Report per-file counts for one group.  File names are printed relative
    to `root` (the group's own directory, when it has one, since the group
    heading already names it)."""
    total = Counts()
    print(f"\n## {title}")
    print(f"{'file':{NAMEW}} {'trusted':>8} {'aux-def':>8} {'aux-lem':>8} "
          f"{'proof':>8} {'other':>8} {'total':>8}")
    print("-" * W)
    for path in files:
        c = count_file(path, fsti_lemma_set_for(path))
        total += c
        print(_row(os.path.relpath(path, root), c))
    print("-" * W)
    print(_row("SUBTOTAL", total))
    return total


def pct(part: int, whole: int) -> str:
    return f"{(100.0 * part / whole):.0f}%" if whole else "n/a"


def breakdown(label: str, c: Counts) -> None:
    sp = c.spec + c.proof
    print(f"\n{label}")
    print(f"  trusted spec     : {c.trusted:>6}  ({pct(c.trusted, sp)})")
    print(f"  auxiliary defs   : {c.aux_def:>6}  ({pct(c.aux_def, sp)})")
    print(f"  auxiliary lemmas : {c.aux_lemma:>6}  ({pct(c.aux_lemma, sp)})")
    print(f"  proof            : {c.proof:>6}  ({pct(c.proof, sp)})")
    print(f"  total counted    : {sp:>6}")
    print(f"  (boilerplate/comments/blank: {c.boilerplate})")


def report_example(ex: Example) -> tuple[Counts, Counts]:
    """Report one example.

    Returns ``(example_counts, adversary_core_counts)``.  The example-specific
    adversary core (the Senc/Aenc modules) is reported separately and is *not*
    folded into the returned example counts.
    """
    print("\n" + "#" * W)
    print(f"# {ex.title}")
    print("#" * W)

    rel_dir = os.path.relpath(ex.example_dir, REPO)
    example = report_group(
        f"{ex.key.upper()} example ({rel_dir}/)",
        dir_fstar_files(ex.example_dir),
        root=ex.example_dir,
    )
    core = report_group(
        ex.core_title,
        [p for b in ex.specific_core for p in module_files(b)],
    )

    breakdown(f"{ex.key.upper()} example (excludes {ex.core_title.lower()}):", example)
    return example, core


def report_shared() -> Counts:
    print("\n" + "#" * W)
    print("# Shared infrastructure (used by both examples)")
    print("#" * W)
    core = report_group(
        "Shared core infrastructure",
        [p for b in SHARED_CORE for p in module_files(b)],
    )
    helpers = report_group("Shared helpers (helpers/)",
                           dir_fstar_files(SHARED_HELPERS_DIR),
                           root=SHARED_HELPERS_DIR)
    shared = Counts()
    shared += core
    shared += helpers
    return shared


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "examples", nargs="*", metavar="EXAMPLE",
        help=f"Which example(s) to report: {', '.join(EXAMPLES)}, or all "
             "(default: all).",
    )
    args = parser.parse_args()

    requested = args.examples or ["all"]
    bad = [k for k in requested if k not in EXAMPLES and k != "all"]
    if bad:
        parser.error(f"unknown example(s): {', '.join(bad)} "
                     f"(choose from {', '.join(EXAMPLES)}, all)")

    keys = list(EXAMPLES) if "all" in requested else requested
    selected = [EXAMPLES[k] for k in keys]

    example_counts: dict[str, Counts] = {}
    core_counts: dict[str, Counts] = {}
    for ex in selected:
        example_counts[ex.key], core_counts[ex.key] = report_example(ex)

    shared = report_shared()

    print("\n" + "=" * SUMW)
    print("SUMMARY  (trusted spec / auxiliary definitions / auxiliary lemma "
          "statements / proof)")
    print("=" * SUMW)
    print(f"{'group':{NAMEW}} {'trusted':>8} {'aux-def':>8} {'aux-lem':>8} "
          f"{'proof':>8} {'trust%':>8} {'aux%':>8} {'proof%':>8}")
    print("-" * SUMW)

    def summary_row(label: str, c: Counts) -> None:
        sp = c.spec + c.proof
        print(f"{label[:NAMEW]:{NAMEW}} {c.trusted:>8} {c.aux_def:>8} "
              f"{c.aux_lemma:>8} {c.proof:>8} "
              f"{pct(c.trusted, sp):>8} {pct(c.aux, sp):>8} {pct(c.proof, sp):>8}")

    for ex in selected:
        summary_row(ex.title, example_counts[ex.key])
    for ex in selected:
        summary_row(ex.core_title, core_counts[ex.key])
    summary_row("Shared infrastructure (counted once)", shared)
    print("-" * SUMW)

    grand = Counts()
    for ex in selected:
        grand += example_counts[ex.key]
        grand += core_counts[ex.key]
    grand += shared
    summary_row("TOTAL (examples + shared)", grand)

    if _admitted_found:
        print("\nAdmitted (axiomatized) declarations, counted as trusted spec:")
        for name in sorted(_admitted_found):
            print(f"  {name}")

    warn_stale_trusted_config()


def warn_stale_trusted_config() -> None:
    """Report `TRUSTED` entries that match nothing in the sources we just read.

    An entry can go stale two ways: the module was renamed/removed, or a named
    declaration was.  Either way the affected lines silently fall back to
    "auxiliary", which is exactly the kind of quiet drift a paper-facing number
    should not have.  Only modules that were actually visited are checked, so
    reporting a single example does not flag the other one.
    """
    stale: list[str] = []
    for base, cfg in TRUSTED.items():
        seen = _seen_decl_names.get(base)
        if seen is None:
            continue  # module not part of this run (or renamed -- see below)
        missing = sorted(configured_names(cfg) - seen)
        if missing:
            stale.append(f"  {base}: {', '.join(missing)}")
    unvisited = [b for b in TRUSTED if not module_files_exist(b)]
    if unvisited:
        stale.extend(f"  {b}: module not found" for b in sorted(unvisited))
    if stale:
        print("\nWARNING: stale TRUSTED entries (renamed or removed?):")
        print("\n".join(stale))


def module_files_exist(base: str) -> bool:
    return any(os.path.exists(os.path.join(REPO, base + ext))
               for ext in (".fst", ".fsti"))


if __name__ == "__main__":
    main()
