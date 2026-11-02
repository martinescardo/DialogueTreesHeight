# Tools

Three scripts, run from the top of the repository. Two of them read the
numbering of the paper's items from `latex/dialogue-tree-height.aux`,
which a build of the paper writes, so build the paper before running
them.

## Keeping the companion in step with the paper

The module `source/DialogueTreesHeight/Article.lagda` is the companion
of the paper: an entry for every numbered item, named after the number
the item has in the paper and anchored to its LaTeX label by a comment,
and an entry for every claim the prose makes, named after the argument
of the `\claim` macro that marks the claim in the LaTeX source.

    tools/renumber-companion.py latex/dialogue-tree-height.aux source/DialogueTreesHeight/Article.lagda [--apply]

Renames the entries whose names no longer match the numbers the paper
gives their items, and updates the numbers cited in the companion's
prose. The labels do not change when the numbering does, so they are
what says which entry is which. Without `--apply` it only reports what
it would do. Sub-numbers within an item list are not in the `.aux` and
are not touched.

    tools/audit-companion.py latex/dialogue-tree-height.aux source/DialogueTreesHeight/Article.lagda latex/dialogue-tree-height.claims

Checks the companion against the paper in both directions, so that
nothing of the paper is missing from it and nothing survives in it that
the paper has dropped. Seven checks, described at the head of the
script. The sixth compares the claims the paper writes to
`dialogue-tree-height.claims` as it is typeset with the `-- claim`
lines of the companion, in order. The seventh reads each entry's
definition and asks whether the paper names what it is built from,
which is what catches an entry that outlives the material it
formalizes. An entry supported by the paper's prose rather than by a
pointer is listed in `REVIEWED` in the script, with the reason. Exits
non-zero when anything is found.

`paperlabels.py` holds what the two have in common, which is how to get
the kind, the number and the nesting of a label out of the `.aux` and
the source, and which Agda names the paper cites.
