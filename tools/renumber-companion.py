#!/usr/bin/env python3
"""Renumber the entries of the companion Agda file after the paper's
numbering changes.

Each entry of DialogueTreesHeight.Article is named
after the number its item has in the paper, and carries the LaTeX label
of that item as a comment anchor on the line before it. The label does
not change when the numbering does, so the label is what tells us the
new number. We read the numbers from the .aux file of a build of the
paper and rename every entry whose name no longer agrees.

The prose of the companion cites the items of the paper by number too.
Each paragraph that does so is followed by a line beginning with
Labels, pairing every number in the paragraph with the label it comes
from, as in

  Labels: Remark 5.3 = rem:last-grade, Definition 5.2 = def:cascade,
  Lemma 5.6 = lem:cascade-ops.

A pair may name an item within an item list on both sides, as in

  Lemma 5.10(4) = lem:calculus(item:orbit),

and then the number in the parentheses is renumbered as well. We update
the numbers of each such paragraph, and of the table itself, from the
same .aux file.

Usage:

  tools/renumber-companion.py PAPER.AUX COMPANION.lagda [--apply]

Without --apply it only reports what it would rename.
"""

import re
import sys

KINDS = ("Definition", "Lemma", "Theorem", "Proposition", "Corollary",
         "Example", "Examples", "Remark", "Notation", "Question")

LABEL = re.compile(r"\b([a-z]+:[A-Za-z0-9-]+)")


def anchor_of(line):
    """The label an anchor comment names, or None. An anchor may run
    over two lines, the second of which often begins with the label of
    an item, as in

      -- lem:compact-pt (1), item:compact-and-pointed, against
      -- (2), item:universal-witness

    so the label of the item list is preferred over that of an item,
    and a line naming only items leaves the anchor as it stood."""
    found = LABEL.findall(line)
    for label in found:
        if not label.startswith("item:"):
            return label
    return None
NEWLABEL = re.compile(r"\\newlabel\{([^}]+)\}\{\{([0-9]+(?:\.[0-9]+)*)\}")
# An entry name may stand alone on its line, with the colon of its
# signature on the next, and a definition may take arguments before
# the equals sign, so neither can be required here. Prose is excluded
# by matching only inside code blocks.
ENTRY = re.compile(r"^(" + "|".join(KINDS) + r")-([0-9]+)-([0-9]+)([^\s:=]*)")

# One pairing of a displayed reference with the label it comes from.
PAIR = re.compile(r"""
    (?P<kind>[A-Za-z][A-Za-z ]*?)\s+          # Remark, Open question, ...
    (?P<num>[0-9]+(?:\.[0-9]+)*)              # 6.30
    (?:\((?P<item>[0-9]+)\))?                 # optional (4)
    \s*=\s*
    (?P<label>[a-z]+:[A-Za-z0-9-]+)           # rem:micro-inf-strengthens
    (?:\((?P<ilabel>item:[A-Za-z0-9-]+)\))?   # optional (item:...)
    """, re.VERBOSE)


def numbers_from_aux(path):
    "label -> number, for the numbered environments of the paper"
    table = {}
    for line in open(path):
        for label, num in NEWLABEL.findall(line):
            table.setdefault(label, num)
    return table


def renames(lines, table):
    "the renamings the file needs, as a list of (old, new, line number)"
    out = []
    seen = set()
    anchor = None
    incode = False
    for i, line in enumerate(lines, 1):
        if line.startswith("\\begin{code}"):
            incode = True
            continue
        if line.startswith("\\end{code}"):
            incode = False
            anchor = None
            continue
        if not incode:
            continue
        if line.startswith("--"):
            if line.startswith("-- claim "):
                anchor = None
            else:
                anchor = anchor_of(line) or anchor
            continue
        entry = ENTRY.match(line)
        if not entry:
            continue
        kind, major, minor, suffix = entry.groups()
        old = f"{kind}-{major}-{minor}{suffix}"
        if old in seen:
            continue
        seen.add(old)
        if anchor is None or "." not in table.get(anchor, ""):
            continue
        new = f"{kind}-{table[anchor].replace('.', '-')}{suffix}"
        if new != old:
            out.append((old, new, i))
    return out


def code_lines(lines):
    "the lines inside code blocks, which is where the entries are"
    incode = False
    for line in lines:
        if line.startswith("\\begin{code}"):
            incode = True
        elif line.startswith("\\end{code}"):
            incode = False
        elif incode:
            yield line


def tables(lines):
    """The label tables of the prose, as a list of

       (first line, last line, scope start, text),

    all one-based and inclusive. The scope of a table is the prose it
    follows, which reaches back to the end of the last code block, or
    to the end of the table before it, whichever is nearer."""
    out = []
    start = 1
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("\\end{code}") or line.startswith("\\begin{code}"):
            start = i + 2
        elif line.startswith("Labels:"):
            first = i + 1
            while i + 1 < len(lines) and lines[i + 1].strip():
                i += 1
            last = i + 1
            out.append((first, last, start, "\n".join(lines[first - 1:last])))
            start = last + 1
        i += 1
    return out


def retexts(lines, table):
    "the prose renumberings, as a list of (scope, old, new, line number)"
    out = []
    for first, last, start, text in tables(lines):
        for m in PAIR.finditer(text):
            kind, num, item = m.group("kind"), m.group("num"), m.group("item")
            label, ilabel = m.group("label"), m.group("ilabel")
            if label not in table:
                print(f"{first:>6}  no number for {label}", file=sys.stderr)
                continue
            new_num = table[label]
            new_item = item
            if ilabel is not None:
                if ilabel not in table:
                    print(f"{first:>6}  no number for {ilabel}",
                          file=sys.stderr)
                    continue
                new_item = table[ilabel]
            old = num + (f"({item})" if item else "")
            new = new_num + (f"({new_item})" if new_item else "")
            if new != old:
                out.append(((start, last), kind, old, new, first))
    return out


def apply_retexts(lines, todo):
    "rewrite the numbers in place, within the scope of each table"
    for (start, last), kind, old, new, _ in todo:
        # The kind word may be split from its number across a line
        # break, so the two are matched with the whitespace between
        # them free, and that whitespace is kept as it was.
        # A number is not the one we are after when a digit follows
        # it, directly or after a dot, as 7 does not match Section 7.3.
        tail = r"(?!\d)(?!\.\d)"
        pattern = re.compile(re.escape(kind) + r"(\s+)" + re.escape(old) + tail)
        for i in range(start - 1, last):
            lines[i] = pattern.sub(lambda m: kind + m.group(1) + new, lines[i])
        # A reference wrapped across lines, with the kind word ending
        # one line and the number starting the next.
        for i in range(start - 1, last - 1):
            if re.search(re.escape(kind) + r"\s*$", lines[i]) and \
               re.match(r"\s*" + re.escape(old) + tail, lines[i + 1]):
                lines[i + 1] = re.sub(
                    r"^(\s*)" + re.escape(old) + tail,
                    lambda m: m.group(1) + new, lines[i + 1])
    return lines


def main(argv):
    if len(argv) < 3:
        sys.exit(__doc__)
    aux, companion = argv[1], argv[2]
    apply = "--apply" in argv[3:]

    table = numbers_from_aux(aux)
    text = open(companion).read()
    lines = text.split("\n")
    todo = renames(lines, table)
    prose = retexts(lines, table)

    if not todo and not prose:
        print("nothing to renumber")
        return

    existing = set(m.group(1) + "-" + m.group(2) + "-" + m.group(3) + m.group(4)
                   for m in (ENTRY.match(l) for l in code_lines(lines)) if m)
    moving = {old for old, _, _ in todo}
    for old, new, line in todo:
        clash = " CLASH" if new in existing and new not in moving else ""
        print(f"{line:>6}  {old} -> {new}{clash}")
    for _, kind, old, new, line in prose:
        print(f"{line:>6}  prose: {kind} {old} -> {kind} {new}")
    if any(new in existing and new not in moving for _, new, _ in todo):
        sys.exit("refusing to rename onto an existing entry")

    if not apply:
        print(f"\n{len(todo) + len(prose)} renamings, not applied (pass --apply)")
        return

    if prose:
        lines = apply_retexts(lines, prose)
        text = "\n".join(lines)

    # Rename in two passes, through fresh placeholders, so that a chain
    # such as 2-16 -> 2-15 -> 2-14 cannot have one step undo another.
    for n, (old, _, _) in enumerate(todo):
        text = re.sub(rf"(?<![\w'-]){re.escape(old)}(?![\w'-])",
                      f"\0{n}\0", text)
    for n, (_, new, _) in enumerate(todo):
        text = text.replace(f"\0{n}\0", new)
    open(companion, "w").write(text)
    print(f"\n{len(todo) + len(prose)} renamings applied")


if __name__ == "__main__":
    main(sys.argv)
