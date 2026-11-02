#!/usr/bin/env python3
"""What the other tools need to know about the paper's labels.

The numbers come from the .aux file of a build. Cleveref writes, for
every label, a second entry recording the kind of environment and the
number, as in

  \\newlabel{thm:iota@cref}{{[theorem][23][6]6.23}{[1][51][]51}{}{}{}}

and an item of an enumerate is stamped [enumi] rather than [item], so
the two can be told apart. An item carries only its own number within
the list, so its position in the paper is that of the statement that
contains it, which is read off the sources.
"""

import re

NUMBERED = {"theorem", "definition", "lemma", "proposition", "corollary",
            "example", "examples", "remark", "notation", "question"}

KIND_OF = {"definition": "Definition", "lemma": "Lemma", "theorem": "Theorem",
           "proposition": "Proposition", "corollary": "Corollary",
           "example": "Example", "examples": "Examples", "remark": "Remark",
           "notation": "Notation", "question": "Question"}

# The paper is a single file.
SOURCES = ["latex/dialogue-tree-height.tex"]

ENVS = "|".join(sorted(NUMBERED))
BEGIN = re.compile(r"\\begin\{(" + ENVS + r")\}")
END = re.compile(r"\\end\{(" + ENVS + r")\}")
REF = re.compile(r"\\(?:C|c)?ref\{([^}]+)\}|\\labelcref\{([^}]+)\}")
LABEL = re.compile(r"\\label\{([^}]+)\}")

# The Agda identifiers the paper names, in \\Agda{Module}{name} and in the
# bare \\texttt{name} of a continuation entry. A module-qualified pointer
# also counts as naming the identifier alone.
# An identifier may contain \^{}, the escape for a caret, so a brace
# inside that escape does not end the argument.
AGDA = re.compile(r"\\Agda\{([^}]*)\}\{((?:[^{}]|\\\^\{\})*)\}")
TT = re.compile(r"\\texttt\{((?:[^{}]|\\\^\{\})*)\}")

CREF = re.compile(r"\\newlabel\{([^}]+)@cref\}"
                  r"\{\{\[([a-z]+)\]\[[^\]]*\]\[[^\]]*\]([0-9.]+)\}")
PLAIN = re.compile(r"\\newlabel\{([^}]+)\}\{\{([0-9]+(?:\.[0-9]+)*)\}")


def unescape(ident):
    "an Agda identifier as the LaTeX source writes it, with the escapes undone"
    return ident.replace("\\_", "_").replace("\\^{}", "^").strip()


class Paper:
    "the labels of the paper, their kinds, their numbers and their nesting"

    def __init__(self, aux, sources=SOURCES):
        self.kind, self.number = {}, {}
        for line in open(aux):
            for lab, k, n in CREF.findall(line):
                if lab not in self.kind:
                    self.kind[lab], self.number[lab] = k, n
            for lab, n in PLAIN.findall(line):
                self.number.setdefault(lab, n)
        self.parent = {}
        self.agda = set()
        cur = None
        for path in sources:
            source = open(path, encoding="utf-8").read()
            for module, ident in AGDA.findall(source):
                self.agda.add(module.strip())
                self.agda.add(unescape(ident))
            for ident in TT.findall(source):
                self.agda.add(unescape(ident))
            for line in source.split("\n"):
                for lab in LABEL.findall(line):
                    if self.kind.get(lab) in NUMBERED:
                        cur = lab
                    elif self.kind.get(lab, "").startswith("enum") and cur:
                        self.parent[lab] = cur
        self.agda.discard("")
        for ident in list(self.agda):
            if "." in ident:
                self.agda.add(ident.rsplit(".", 1)[1])
            if "_" in ident.strip("_"):      # a mixfix name, "retract_of_",
                self.agda.update(ident.split("_"))   # applied as its parts

    def is_item(self, lab):
        return self.kind.get(lab) in NUMBERED

    def statement(self, lab):
        "the numbered statement a label denotes or belongs to, or None"
        if self.is_item(lab):
            return lab
        return self.parent.get(lab)

    def order(self, lab):
        return tuple(int(x) for x in self.number[lab].split("."))

    def refs(self, text):
        "the labels cited in a piece of source, one entry per citation"
        for m in REF.finditer(text):
            for group in m.groups():
                if not group:
                    continue
                for lab in group.split(","):
                    yield lab.strip(), text[:m.start()].count("\n")
