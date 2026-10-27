# The dialogue trees of system T have height below ε₀, and this bound is sharp

The [dialogue interpretation](https://doi.org/10.1016/j.entcs.2013.09.010)
(MFPS 2013) of Gödel's system T assigns to each closed term of type
`(ι ⇒ ι) ⇒ ι` a well founded tree, branching over the natural numbers,
whose nodes record the queries the term makes to its oracle. It was
internalized in system T itself, with dialogue trees given by Church
encodings, by Escardó, da Rocha Paiva, Rahli and Tosun,
[FSCD 2025](https://doi.org/10.4230/LIPIcs.FSCD.2025.19). This
repository holds an Agda formalization of the following two results,
generated with the help of LLM's, and a paper presenting them.

1. The height of the dialogue tree of every such term, measured as a
   Brouwer ordinal code, is below `ε₀`.
2. The bound `ε₀` is the least one: for every `n` there is a term whose
   dialogue tree has height at least the `n`-th approximant
   `ω^ω^…^ω` of `ε₀`.

The development is constructive, checked with `--safe` and
`--without-K`, with no postulates and no holes, and its only
assumption is function extensionality.

* [The formalization, rendered as html](https://martinescardo.github.io/DialogueTreesHeight/)
* [The paper, as pdf](https://martinescardo.github.io/DialogueTreesHeight/dialogue-tree-height.pdf)

The paper and the formalization in this repository were developed by
LLM's under Martín Escardó's direction. He has verified the correctness
of the formulation of the main theorems in the Agda code and takes
responsibility for this. However, he takes no responsibility for the
correctness of the paper, but see the precautions taken in its
[Appendix A][pdf]. The paper would greatly benefit from further human
care.

## Related work

Xiao and Sun, [arXiv:2609.20369](https://arxiv.org/abs/2609.20369) (17
September 2026), have proved the same upper bound, with a computable
tower level for each term, over ordinals using classical logic. They
claim an Agda formalization using TypeTopology, but it isn't linked in
the paper and we haven't been able to find it. The proof we offer is
constructive, measuring heights by Brouwer codes instead, and it
settles the sharpness question that they leave open.

## The structure of the repository

* [`source/DialogueTreesHeight/index.lagda`](https://github.com/martinescardo/DialogueTreesHeight/blob/master/source/DialogueTreesHeight/index.lagda)
  imports every module in dependency order and ends with an outline of
  the proof and the references.
* [`source/DialogueTreesHeight/BrouwerOrdinals`](https://github.com/martinescardo/DialogueTreesHeight/tree/master/source/DialogueTreesHeight/BrouwerOrdinals),
  17 modules, holds the ordinal arithmetic of Brouwer codes and the
  graded maps used to bound the majorants, and doesn't rely on system T
  or dialogue trees.
* [`source/DialogueTreesHeight/DialogueTrees`](https://github.com/martinescardo/DialogueTreesHeight/tree/master/source/DialogueTreesHeight/DialogueTrees),
  10 modules, defines the height of a dialogue tree, assigns a majorant
  to every term, proves the bound, and constructs the terms that attain
  the approximants of `ε₀`.
* [`latex/dialogue-tree-height.tex`](https://github.com/martinescardo/DialogueTreesHeight/blob/master/latex/dialogue-tree-height.tex)
  is the paper. Every result in it carries a pointer to the Agda
  definition that proves it.

The dialogue trees, the combinatory system T and its dialogue
interpretation come from the module
[`EffectfulForcing.MFPSAndVariations`][MFPSAndVariations] of
[TypeTopology](https://github.com/martinescardo/TypeTopology), and the
Brouwer codes from its module [`Ordinals.BrouwerCodes`][BrouwerCodes].

## How the formalization was pruned

The attempts to prove the upper bound produced 118 Agda modules, with
28,615 lines, of which 14,813 are nonblank lines of code and 6,399
nonblank lines of prose, the rest being blank lines, comments and the
delimiters of code blocks. The LLM's wrote the prose of their own
accord, following the literate style of TypeTopology, without being
asked to. Besides the proof, the modules hold the routes that were tried
and abandoned, and a classical treatment over ordinals.

The pruning started from the module [`Fundamental`][Fundamental], which
proves the upper bound, and kept only the modules it imports, directly
or indirectly. That left 34 modules, with 8,167 lines, of which 4,325
are code, and discarded the other 84 outright.

Within those 34 modules, the pruning then worked on definitions. A
program read off, for each top-level definition, the definitions its
code mentions, and removed every definition that the theorem doesn't
reach in the resulting graph. The program reads names rather than types,
so its verdict wasn't taken on trust: the development was typechecked
again after each round of removals, and the rounds were repeated until
nothing more went. Then each surviving definition was deleted in turn
and kept only if the development then failed to typecheck. This took 335
typechecks and found four more definitions to remove. Of the 554
top-level definitions in the 34 modules, 333 are used by the proof and
221 aren't. The result is minimal in the sense that no single definition
can be removed, which doesn't exclude that several could be removed
together.

Next, the 205 imported names that were no longer used were removed,
together with 41 whole import statements, again typechecking after each
step. One more module was then imported by nothing, and it was deleted
together with the modules that the pruning had emptied. The 71
paragraphs of prose that introduced emptied code blocks were cut, and
the modules whose names no longer fitted their contents were renamed or
merged. The remaining prose was then rewritten throughout. A second run
of the one-at-a-time check, after these steps, was stopped after 100 of
the 330 remaining definitions, having found nothing to remove. This
leaves 24 modules, with 4,668 lines, of which 2,555 are code.

Two things went wrong along the way, and both were caught. Removing
imports once emptied the index, so that later typechecks checked
nothing and the one-at-a-time check deleted almost everything, and Agda
once reused stale interface files instead of checking the edited
sources. Both passes were run again with Agda made to check the edited
sources each time, and the final development was checked from deleted
interface files.

The sharpness results were proved afterwards, in the modules
[`Examples`][Examples] and [`Sharpness`][Sharpness]. Together with
[`Main`][Main] and the index, they bring the development to the 28
modules here, with 5,643 lines, of which 2,985 are code.

| stage | modules | lines | lines of code | lines of prose |
| --- | ---: | ---: | ---: | ---: |
| everything the attempts produced | 118 | 28,615 | 14,813 | 6,399 |
| the modules the proof of the upper bound imports | 34 | 8,167 | 4,325 | 1,394 |
| those modules, pruned | 24 | 4,668 | 2,555 | 693 |
| **this repository**: the pruned modules with the sharpness results | **28** | **5,643** | **2,985** | **955** |

## The main theorems

The four results are proved in two modules of
[`DialogueTrees`][DialogueTrees] and restated independently in its
module [`Main`][Main].

| result | proved in | restated in |
| --- | --- | --- |
| upper bound | [`Fundamental.dialogue-tree-height-<-ε₀`][Fundamental] | [`Main.restated`][Main] |
| lower bound | [`Sharpness.tower-attained`][Sharpness] | [`Main.attained`][Main] |
| cofinality | [`Sharpness.heights-cofinal`][Sharpness] | [`Main.cofinal`][Main] |
| least bound | [`Sharpness.ε₀-least`][Sharpness] | [`Main.least`][Main] |

To trust the results, it's enough to read their statements, which are
the four types in `Main`, together with the type `T ((ι ⇒ ι) ⇒ ι)` they
quantify over and the definitions they're built from. These are the
order and the arithmetic of Brouwer codes in the modules
[`Order`][Order], [`Multiplication`][Multiplication] and
[`Epsilon0`][Epsilon0], the height of a dialogue tree in
[`Constructive`][Constructive], and [`dialogue-tree`][dialogue-tree] in
TypeTopology, some twenty lines in all. The module `Main` writes the
statements out with the abbreviations unfolded, checks that the type
quantified over is inhabited and that the order isn't degenerate, and
checks by `refl` that the approximants of `ε₀` are `ω`, `ω^ω`, `ω^ω^ω`,
and so on, with `ε₀` their limit.

## Typechecking

The development was checked with Agda 2.9.0 against TypeTopology at
commit
[`ee4e4c86`](https://github.com/martinescardo/TypeTopology/commit/ee4e4c86da34ac609389285baa01e2eab6062b37).
With TypeTopology registered as a library in `~/.agda/libraries`, run

    cd source
    agda --safe DialogueTreesHeight/index.lagda

The html and the pdf are produced by the workflow in
[`.github/workflows/pages.yml`][workflow], which typechecks the
development against the same commit of TypeTopology, renders it with the
script [`agda-html.py`][agda-html] of TypeTopology, and compiles the
paper.

## License

This work is licensed under the
[Creative Commons Attribution 4.0 International License](https://creativecommons.org/licenses/by/4.0/),
whose full text is in the file [`LICENSE`][LICENSE]. It may be used,
shared and adapted for any purpose, provided that appropriate credit is
given.

[pdf]: https://martinescardo.github.io/DialogueTreesHeight/dialogue-tree-height.pdf
[MFPSAndVariations]: https://github.com/martinescardo/TypeTopology/tree/ee4e4c86da34ac609389285baa01e2eab6062b37/source/EffectfulForcing/MFPSAndVariations
[BrouwerCodes]: https://github.com/martinescardo/TypeTopology/blob/ee4e4c86da34ac609389285baa01e2eab6062b37/source/Ordinals/BrouwerCodes.lagda
[dialogue-tree]: https://github.com/martinescardo/TypeTopology/blob/ee4e4c86da34ac609389285baa01e2eab6062b37/source/EffectfulForcing/MFPSAndVariations/MFPS-XXIX.lagda
[agda-html]: https://github.com/martinescardo/TypeTopology/blob/43157f4b32b1fc272739596f2116878fbfca6760/admin-utilities/agda-html.py
[DialogueTrees]: https://github.com/martinescardo/DialogueTreesHeight/tree/master/source/DialogueTreesHeight/DialogueTrees
[Fundamental]: https://github.com/martinescardo/DialogueTreesHeight/blob/master/source/DialogueTreesHeight/DialogueTrees/Fundamental.lagda
[Examples]: https://github.com/martinescardo/DialogueTreesHeight/blob/master/source/DialogueTreesHeight/DialogueTrees/Examples.lagda
[Sharpness]: https://github.com/martinescardo/DialogueTreesHeight/blob/master/source/DialogueTreesHeight/DialogueTrees/Sharpness.lagda
[Main]: https://github.com/martinescardo/DialogueTreesHeight/blob/master/source/DialogueTreesHeight/DialogueTrees/Main.lagda
[Constructive]: https://github.com/martinescardo/DialogueTreesHeight/blob/master/source/DialogueTreesHeight/DialogueTrees/Constructive.lagda
[Order]: https://github.com/martinescardo/DialogueTreesHeight/blob/master/source/DialogueTreesHeight/BrouwerOrdinals/Order.lagda
[Multiplication]: https://github.com/martinescardo/DialogueTreesHeight/blob/master/source/DialogueTreesHeight/BrouwerOrdinals/Multiplication.lagda
[Epsilon0]: https://github.com/martinescardo/DialogueTreesHeight/blob/master/source/DialogueTreesHeight/BrouwerOrdinals/Epsilon0.lagda
[workflow]: https://github.com/martinescardo/DialogueTreesHeight/blob/master/.github/workflows/pages.yml
[LICENSE]: https://github.com/martinescardo/DialogueTreesHeight/blob/master/LICENSE
