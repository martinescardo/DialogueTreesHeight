#!/usr/bin/env python3
"""Check the companion Agda file against the paper, in both directions.

Nothing of the paper should be missing from the companion, and nothing
should be left in it that the paper no longer has. Six checks:

  1 every numbered item of the paper has an entry anchored to its label,
    or is named in one of the prose Labels tables;
  2 every label an anchor names is still a label of the paper, and so is
    every label a Labels table names;
  3 each entry name agrees with the kind and number of its anchor;
  4 each sub-number in an anchor agrees with the number the item has;
  5 no name is declared twice, which renumbering can bring about when it
    strands the primed companion of a renamed entry;
  6 the claims of the paper and the "-- claim" lines agree, in order;
  7 every entry is defined from something the paper names, which is what
    anchors it: an entry inherits the anchor of the one above it, so a
    primed or suffixed entry can outlive the material it formalizes
    without any of checks 1-3 noticing. An
    entry proved by refl states a definitional identity and cites no
    name, so it is passed.

An entry name may stand alone on its line, with the colon of its
signature on the next, and a definition may take arguments before the
equals sign, so neither can be required when looking for one. An entry
may be indented, inside a module that takes a local hypothesis. An anchor
may likewise run over two comment lines, with the item label opening the
second, which check 4 reads as one. Prose is excluded by reading only
inside the code blocks.

Usage:

  tools/audit-companion.py PAPER.AUX COMPANION.lagda PAPER.claims [PAPER.tex]
"""

import collections
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from paperlabels import KIND_OF, NUMBERED, SOURCES, Paper  # noqa: E402

KINDS = tuple(KIND_OF.values()) + ("Prose",)
ENTRY = re.compile(r"^(" + "|".join(KINDS) + r")([^\s:=]*)")
LABEL = re.compile(r"\b([a-z]+:[A-Za-z0-9-]+)")
SUBITEM = re.compile(r"^--\s*([a-z]+:[A-Za-z0-9-]+)\s*\((\d+)\)\s*,\s*"
                     r"(item:[A-Za-z0-9-]+)")
# The same pairing split over two comment lines, the item label opening
# the second, as in
#
#   -- prop:discrete-exponential-gives-compact (1),
#   -- item:disconnected-power-compact
#
# which a long label can force. Without this the sub-number of such an
# anchor goes unchecked.
# The right-hand side of a definition, for check 7. A name written with
# underscore placeholders or brackets, "_↔_", "⟨_⟩", "⟦_⟧-sup", is
# notation that the paper displays rather than cites by name, so an
# entry defined from one of those is left alone.
DEFN = re.compile(r"^([A-Za-z][^\s:=]*)[^=]*=(.*)$")
IDENT = re.compile(r"[^\s(){};,]+")
NOTATION = re.compile(r"[_⟨⟩⟦⟧]")

# Entries that formalize something the paper states in prose or in a
# display but does not name in an \AgdaRefs, so that check 7 cannot see
# the support. A numbered entry is listed by its anchor and the part of
# its name that follows the number, as in "def:codes|-strict-unfolds",
# since the number itself changes whenever the paper renumbers. A Prose
# entry carries no number, so it is listed by name.
REVIEWED = {
    "def:dialogue-tree-type|-η": "the generator η displayed in the definition",
    "def:dialogue-tree-type|-β": "the generator β displayed in the definition",
    "def:codes|": "the type B of codes, which the development renames 𝓑",
    "def:codes|-Z": "the constructor Z displayed in the definition",
    "def:codes|-S": "the constructor S displayed in the definition",
    "def:codes|-L": "the constructor L displayed in the definition",
    "def:tower-term|-syntax": "the syntax with binders that abs and tm act on",
}


def reviewed(name, anchor):
    """Whether an entry is on the allow-list above, under either the
    name of a Prose entry or the anchor-and-suffix key of a numbered
    one."""
    if name in REVIEWED:
        return True
    # Longest first, or "Examples" is eaten as "Example" and the "s"
    # left behind blocks the number from being stripped.
    kinds = "|".join(sorted(KINDS, key=len, reverse=True))
    suffix = re.sub(r"^(" + kinds + r")(-\d+)*", "", name)
    return f"{anchor}|{suffix}" in REVIEWED

SUBITEM_HEAD = re.compile(r"^--\s*([a-z]+:[A-Za-z0-9-]+)\s*\((\d+)\)\s*,\s*$")
SUBITEM_TAIL = re.compile(r"^--\s*(item:[A-Za-z0-9-]+)")


def read(path):
    """The companion, as its anchors, entries, claims and Labels tables.

    An anchor is the label named on a "--" line, preferring the label of
    a list over that of one of its items, so that an anchor running over
    two lines is not lost when the second names only items."""
    lines = open(path, encoding="utf-8").read().split("\n")
    anchors = collections.defaultdict(list)
    entries, claims, subitems = [], [], []
    tabled = set()
    anchor, incode, intable, pending = None, False, False, None
    for i, line in enumerate(lines, 1):
        if line.startswith("Labels:"):
            intable = True
        elif not line.strip():
            intable = False
        if intable:
            tabled.update(LABEL.findall(line))
        if line.startswith("\\begin{code}"):
            incode = True
            continue
        if line.startswith("\\end{code}"):
            incode, anchor, pending = False, None, None
            continue
        if not incode:
            continue
        line = line.lstrip()
        if line.startswith("--"):
            if line.startswith("-- claim "):
                claims.append(line[len("-- claim "):].strip())
                anchor, pending = None, None
            else:
                for lab in LABEL.findall(line):
                    anchors[lab].append(i)
                named = [x for x in LABEL.findall(line)
                         if not x.startswith("item:")]
                if named:
                    anchor = named[0]
                m = SUBITEM.match(line)
                head = SUBITEM_HEAD.match(line)
                tail = SUBITEM_TAIL.match(line) if pending else None
                if m:
                    subitems.append((i, m.group(1), m.group(2), m.group(3)))
                    pending = None
                elif head:
                    pending = (i, head.group(1), head.group(2))
                elif tail:
                    subitems.append(pending + (tail.group(1),))
                    pending = None
                else:
                    pending = None
            continue
        pending = None
        m = ENTRY.match(line)
        if m:
            entries.append((i, m.group(1) + m.group(2), anchor))
    return anchors, entries, claims, subitems, tabled


def definitions(path):
    """what each entry is defined from, as the names on its right.

    A definition may take arguments before the equals sign and may run
    over several lines, so the block is read to the next blank line."""
    lines = open(path, encoding="utf-8").read().split("\n")
    out, incode = {}, False
    for i, line in enumerate(lines):
        if line.startswith("\\begin{code}"):
            incode = True
        elif line.startswith("\\end{code}"):
            incode = False
        line = line.lstrip()
        if not incode or line.startswith("--") or not line.strip():
            continue
        m = DEFN.match(line)
        if not m or m.group(1) in out:
            continue
        rhs, j = [m.group(2)], i + 1
        while j < len(lines) and lines[j].strip() and not lines[j].lstrip().startswith("--"):
            rhs.append(lines[j])
            j += 1
        names = set()
        for tok in IDENT.findall(" ".join(rhs)):
            tok = tok.strip("()")
            if tok:
                names.add(tok)
                if "." in tok:
                    names.add(tok.rsplit(".", 1)[1])
        out[m.group(1)] = names
    return out


def main(argv):
    if len(argv) < 4:
        sys.exit(__doc__)
    paper = Paper(argv[1], [argv[4]] if len(argv) > 4 else SOURCES)
    anchors, entries, claims, subitems, tabled = read(argv[2])
    items = {l: n for l, n in paper.number.items() if paper.is_item(l)}
    bad = 0

    print("1 paper items with no companion entry")
    missing = sorted((n, l) for l, n in items.items()
                     if l not in anchors and l not in tabled)
    for n, l in sorted(missing, key=lambda x: paper.order(x[1])):
        print(f"    {paper.kind[l].capitalize():12} {n:6} {l}")
    print(f"    {len(missing)} of {len(items)}")
    bad += len(missing)

    print("2 labels named in the companion that the paper no longer has")
    stale = [(i, l) for l, ls in anchors.items() for i in ls
             if l not in paper.number]
    stale += [(0, l) for l in sorted(tabled) if l not in paper.number]
    for i, l in sorted(stale):
        print(f"    line {i:>5}  {l}")
    print(f"    {len(stale)}")
    bad += len(stale)

    print("3 entry names that disagree with their anchor")
    n3, checked = 0, set()
    for i, name, anchor in entries:
        if name.startswith("Prose") or anchor is None or name in checked:
            continue
        checked.add(name)
        kind = paper.kind.get(anchor)
        if kind not in KIND_OF:
            continue
        want = KIND_OF[kind] + "-" + paper.number[anchor].replace(".", "-")
        if not name.startswith(want):
            print(f"    line {i:>5}  {name:34} anchored to {anchor}, "
                  f"which is {KIND_OF[kind]} {paper.number[anchor]}")
            n3 += 1
    print(f"    {n3} of {len(checked)} entries")
    bad += n3

    print("4 sub-numbers in anchors that disagree with the paper")
    n4 = 0
    for i, parent, shown, item in subitems:
        if item not in paper.number:
            print(f"    line {i:>5}  {item} is not an item of the paper")
            n4 += 1
        elif paper.number[item] != shown:
            print(f"    line {i:>5}  {parent} ({shown}), but {item} "
                  f"is item {paper.number[item]}")
            n4 += 1
    print(f"    {n4}")
    bad += n4

    print("5 names declared more than once")
    seen = collections.Counter(name for _, name, _ in entries)
    dups = {k: v for k, v in seen.items() if v > 2}
    for k, v in sorted(dups.items()):
        print(f"    {k} on {v} lines")
    print(f"    {len(dups)}")
    bad += len(dups)

    print("6 claims")
    written = [c.strip() for c in open(argv[3]) if c.strip()]
    if written == claims:
        print(f"    {len(written)} agree, in order")
    else:
        for c in written:
            if c not in claims:
                print(f"    missing from the companion: {c}")
                bad += 1
        for c in claims:
            if c not in written:
                print(f"    no longer in the paper:     {c}")
                bad += 1

    print("7 entries defined from nothing the paper names")
    n7 = 0
    defined = definitions(argv[2])
    seen7 = set()
    for i, name, anchor in entries:
        if name in seen7:
            continue
        seen7.add(name)
        names = defined.get(name, set())
        if not names or names & paper.agda:
            continue
        if names <= {"refl"}:
            # a definitional identity, which cites no name of the paper
            continue
        if any(NOTATION.search(x) for x in names) or reviewed(name, anchor):
            continue
        print(f"    line {i:>5}  {name:38} [{anchor}]")
        n7 += 1
    print(f"    {n7}")
    bad += n7

    print(f"\n{bad} finding{'' if bad == 1 else 's'}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
