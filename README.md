# The dialogue trees of system T have height below ε₀, and this bound is sharp

27 October 2026

The [dialogue interpretation](https://doi.org/10.1016/j.entcs.2013.09.010)
(MFPS 2013) of Gödel's system T assigns to each closed term of type
`(ι ⇒ ι) ⇒ ι` a well founded tree, branching over the natural numbers,
whose nodes record the queries the term makes to its oracle. It was
internalized in system T itself, with dialogue trees given by Church
encodings, by Escardó, da Rocha Paiva, Rahli and Tosun,
[FSCD 2025](https://doi.org/10.4230/LIPIcs.FSCD.2025.19). This
repository holds an Agda formalization of the following two results,
generated with the help of LLMs, and a paper presenting them.

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

The formalization was developed with the aid of LLMs, and the paper
was then unformalized from it, again with their aid.

## Contents

* [Related work](#related-work)
* [The structure of the repository](#the-structure-of-the-repository)
* [Typechecking](#typechecking)
* [The main theorems](#the-main-theorems)
* [How the formalization was pruned](#how-the-formalization-was-pruned)
* [How the paper was verified](#how-the-paper-was-verified)
  * [The pointers](#the-pointers)
  * [The A/B/C verification](#the-abc-verification)
  * [The independent review](#the-independent-review)
  * [Human verification](#human-verification)
* [License](#license)
* [Citing this work](#citing-this-work)

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
  is the paper. Its source carries, after every result, a pointer to
  the Agda definition that proves it, printed when the switch
  `\agdarefstrue` is set in the preamble.
* [`source/DialogueTreesHeight/Article.lagda`](https://github.com/martinescardo/DialogueTreesHeight/blob/master/source/DialogueTreesHeight/Article.lagda)
  is the Agda companion of the paper: an entry for every numbered item
  of the paper, in the paper's order and under the paper's numbering,
  and for every claim its prose makes, each giving the name in the
  development that proves it, so that you can walk the module alongside
  the paper.
* [`tools`](https://github.com/martinescardo/DialogueTreesHeight/tree/master/tools)
  holds the scripts that keep the companion in step with the paper when
  its numbering changes, and that check the two against each other.

The dialogue trees, the combinatory system T and its dialogue
interpretation come from the module
[`EffectfulForcing.MFPSAndVariations`][MFPSAndVariations] of
[TypeTopology](https://github.com/martinescardo/TypeTopology), and the
Brouwer codes from its module [`Ordinals.BrouwerCodes`][BrouwerCodes].

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

## How the formalization was pruned

The attempts to prove the upper bound produced 118 Agda modules, with
28,615 lines, of which 14,813 are nonblank lines of code and 6,399
nonblank lines of prose, the rest being blank lines, comments and the
delimiters of code blocks. The LLMs wrote the prose of their own
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

## How the paper was verified

The formalization was developed first, by LLMs, and the paper was then
unformalized from it, again by LLMs, each statement of the paper being
written from the Agda statement it points at. This section describes
the pointers that tie the paper to the code, records how the paper was
verified against it, and reports the independent review of the paper
alone and the changes it led to.

Two claims in the paper that something is false, in Remark 5.3 and in
the proof of Lemma 6.3(3), are motivation and aren't formalized, nor is
the remark of Section 8.2 that the natural order is sound for the
standard interpretation of the codes under excluded middle, and the
account of the proof of Xiao and Sun in the same section comes from
reading their paper.

### The pointers

Every numbered item carries a pointer in the LaTeX source to the Agda
that proves it, set in blue when the switch `\agdarefstrue` is on, as it
was during the verification. A pointer names a module and a definition
in it, then further names of the same module, and a name must be defined
in the module it's cited under rather than re-exported by it. A script
resolves every pointer against the sources and reports, for this paper,
64 notes carrying 304 names, all resolving. Four numbered items carry no
pointer, three remarks and a question, which make no formal claim, and
Lemma 6.2 carries a note in place of a lemma, its two sides being
definitionally equal. The paper was written statement first, each Agda
statement being read before the paper's was written, and the proofs
describe the route the Agda takes. The companion module
[`Article`](https://martinescardo.github.io/DialogueTreesHeight/DialogueTreesHeight.Article.html)
ties the two together the other way round, with an entry for every
numbered item and every prose claim of the paper.

### The A/B/C verification

The paper was then verified against the formalization in three passes,
the independence of the first two being the point of the arrangement.

* **A.** Read the paper alone, with the formalization closed, as a
  reader with no access to it: whether the mathematics is correct,
  whether each statement is self-contained, whether each proof proves
  what its statement says in steps that can be followed, and whether
  the prose says what it means. The findings go to a numbered list.
* **B.** Audit the same text against the formalization, without
  opening the list from pass A: each statement against the Agda it
  points at, each proof against the route the Agda takes, and each
  pointer against what exists and in which module.
* **C.** Read the two lists together, merge the findings that coincide,
  drop a finding of A that B refutes, and rank what survives with the
  errors first, the faithfulness gaps next and the language last. Each
  finding is then settled before the next is raised.

On the first run pass A produced sixteen findings and pass B eleven, one
pair merged, and twenty-five survived into pass C, of which five were
errors. They're worth naming as a sample of what each pass catches.
Pass A found an operation used in the statement of a lemma and nowhere
defined, a constant used in four places and nowhere defined, and a
definition that reads as trivially the identity unless one is told why
it isn't. Pass B found a proof attributing two of its cases to a lemma
that neither case uses, a second proof describing a route the Agda
doesn't take, and a theorem stated in a shape weaker than the one the
pointer proves.

The procedure was run more than once, and with more than one model, the
later runs finding no error of mathematics and a small number of
faithfulness gaps and points of language, most of them in text the
first run had added. A limitation of every run should be recorded. The
value of pass A lies in the reader's ignorance of the formalization, and
in each run the model carrying out that pass had the formalization at
hand, so that it could read the paper as it was meant rather than as it
stands. An independent pass A is the single change that would most
strengthen the procedure.

The procedure was run once more after the four rounds of the
independent review below, on the revised paper. It found no error of
mathematics and fourteen points: three of faithfulness, namely that the
soundness of the natural order for the standard interpretation of the
codes was asserted without saying that it's a classical remark and
isn't formalized, that the paper said the development records what
fails without excluded middle when the classical modules had been
discarded in the pruning, and that it said every module takes function
extensionality as a parameter when the index doesn't; and eleven of
precision and language, most of them in the text the revision had
added. The same limitation applied, the model carrying out pass A
having had the formalization at hand.

### The independent review

An independent pass A was then carried out, on 28 October 2026. A copy
of the paper was made with the pointers, the links, the account of the
formalization and every mention of it removed, and it was given to an
LLM that had taken no part in the development, with the request to
referee it for mathematical correctness. The referee was asked not to
consult the internet, and it confirmed that it didn't, which has to be
taken on trust. Its verdict was that the main claims weren't
established by the paper as written, and it recommended a major
revision. It found no counterexample to the bound. It made three
findings, and Martín Escardó, reading the same copy, made a fourth.

1. The reading of a tuple as a graded map was misstated. The paper took
   the cascade of output order `j` to be the whole suffix of the tuple
   from `j`, which is longer than a cascade reading the input orders
   `j` and above as soon as the output is wider than the input by more
   than one. The formalization reads the entries of orders `j` to `p`
   only, as Section 5.3 now says.
2. The four parts of the calculus lemma, Lemma 5.10, were stated
   without proof, and the operations on graded maps that the clauses
   for `S` and the recursor use were called routine and not defined.
   The laws of absorption of Lemma 3.12, the operations on cascades and
   on graded maps, with Lemmas 5.6 and 5.9, and the proof of Lemma 5.10
   now supply them, and the proofs of Lemmas 6.5 and 6.6 now name the
   data they build.
3. The proof of the lower bound, Theorem 7.11, didn't justify its limit
   step. The limit of the algebra applies a function to the tree
   `β η 0`, and a function that ignores its argument makes no query.
   The relation asks about the limit only at Kleisli extensions, and
   the terms pass nothing else to a limit, but the paper said so in a
   single clause and gave neither the encodings nor the relation. Both
   are now written out, in Definitions 7.4 and 7.8, together with the
   preservation lemma, Lemma 7.9.
4. The generic oracle was defined only in passing, in the sentence
   after the definition of dialogue trees. It now has a definition of
   its own, Definition 2.2, with the equations of the Kleisli extension
   it's built from.

None of the four concerns the formalization, which reads tuples as
graded maps, proves the calculus, restricts the relation to Kleisli
extensions and defines the generic oracle as the paper now does, and no
Agda was changed. The first finding is a statement that doesn't match
the definition its pointer names, which pass B of the earlier runs
hadn't caught. The second and third are proofs that the paper had left
to its pointers, which a reader of the paper alone can't follow.

A second copy, made in the same way from the revised paper, was then
given to the same referee, which again stated that it didn't consult
the internet. Its verdict was that the revision resolves the three
findings of its first report, that it found no counterexample to the
main claims, and that the sharpness argument had become substantially
more convincing, and it recommended a minor revision for proof detail.
It asked for two additions.

1. The elementary properties of the order and the laws of the
   arithmetic of codes in Section 3, on which the closure of `ε₀`
   rests, were stated without proof, and the proofs of Lemma 3.9 and
   Proposition 3.11 were sketches. The properties and the laws are now
   Lemmas 3.2 and 3.6 to 3.8, with their proofs, the absorption of sums
   and products by the tower is Lemma 3.10, and the proofs of Lemma 3.9
   and Proposition 3.11 now give every step.
2. The proof of Proposition 7.3 excluded `S ε₀ ≤ ε₀` "by induction on
   the code". The general fact is now Lemma 3.4, with its proof.

Again no Agda was changed. The second reading is less independent than
the first, since the referee had its own first report in view, but it
still had no access to the formalization.

A third copy, made in the same way, was given to the same referee,
which again stated that it didn't consult the internet. It found no
remaining objection to the correctness of the main theorems and
recommended acceptance after minor clarifications, asking for three
proof details, none of which it regarded as a gap.

1. The inequality `n · ω^e ≤ ω^(S e)` in the proof of Lemma 3.12 was
   proved "by induction on `e`". The three cases are now written out,
   the limit case included.
2. The proof of Lemma 6.3 called every part an induction on the type,
   and didn't write out the ground case of the last part. The ground
   cases are now given, and the last part is derived from
   `a ≤ d₀ < ε₀` by the successor rule.
3. The induction in the proof of Proposition 7.2 that the generic
   oracle raises a finite lower bound by one didn't show the step at a
   query node. It's now an induction on the numeral, and the step
   inverts a bound on a limit to a bound on one of its subtrees.

No Agda was changed in this round either.

A fourth copy, made in the same way, was given to the same referee,
which again stated that it didn't consult the internet. It confirmed
that the three clarifications were present, rechecked how the bound on
the iterates feeds the clause for the recursor and how the proof of the
lower bound tests the limit of the algebra on Kleisli extensions, found
no new gap, and recommended acceptance, with no remaining objection to
the correctness of the paper. It added that its assessment is of the
written proof, not a machine-checked verification. No change was asked
for, and none was made.

### Human verification

The author used the Agda companion
[`Article`](https://martinescardo.github.io/DialogueTreesHeight/DialogueTreesHeight.Article.html)
to manually check that the paper matches the formalization. The companion was
written by an LLM to match the two, so this check and the LLM's are
independent.

## License

This work is licensed under the
[Creative Commons Attribution 4.0 International License](https://creativecommons.org/licenses/by/4.0/),
whose full text is in the file [`LICENSE`][LICENSE]. It may be used,
shared and adapted for any purpose, provided that appropriate credit is
given.

## Citing this work

```bibtex
@misc{Escardo2026DialogueTreesHeight,
  author       = {Escard{\'o}, Mart{\'\i}n},
  title        = {The dialogue trees of system {T} have height below
                  $\varepsilon_0$, and this bound is sharp},
  year         = {2026},
  month        = oct,
  howpublished = {\url{https://github.com/martinescardo/DialogueTreesHeight}},
  note         = {An Agda formalization, with a paper, developed with
                  LLMs},
}
```

[pdf]: https://martinescardo.github.io/DialogueTreesHeight/dialogue-tree-height.pdf
[MFPSAndVariations]: https://github.com/martinescardo/TypeTopology/tree/ee4e4c86da34ac609389285baa01e2eab6062b37/source/EffectfulForcing/MFPSAndVariations
[BrouwerCodes]: https://github.com/martinescardo/TypeTopology/blob/ee4e4c86da34ac609389285baa01e2eab6062b37/source/Ordinals/BrouwerCodes.lagda
[dialogue-tree]: https://github.com/martinescardo/TypeTopology/blob/ee4e4c86da34ac609389285baa01e2eab6062b37/source/EffectfulForcing/MFPSAndVariations/MFPS-XXIX.lagda
[agda-html]: https://github.com/martinescardo/TypeTopology/blob/43157f4b32b1fc272739596f2116878fbfca6760/admin-utilities/agda-html.py
[DialogueTrees]: https://github.com/martinescardo/DialogueTreesHeight/tree/master/source/DialogueTreesHeight/DialogueTrees
[Fundamental]: https://martinescardo.github.io/DialogueTreesHeight/DialogueTreesHeight.DialogueTrees.Fundamental.html
[Examples]: https://martinescardo.github.io/DialogueTreesHeight/DialogueTreesHeight.DialogueTrees.Examples.html
[Sharpness]: https://martinescardo.github.io/DialogueTreesHeight/DialogueTreesHeight.DialogueTrees.Sharpness.html
[Main]: https://martinescardo.github.io/DialogueTreesHeight/DialogueTreesHeight.DialogueTrees.Main.html
[Constructive]: https://martinescardo.github.io/DialogueTreesHeight/DialogueTreesHeight.DialogueTrees.Constructive.html
[Order]: https://martinescardo.github.io/DialogueTreesHeight/DialogueTreesHeight.BrouwerOrdinals.Order.html
[Multiplication]: https://martinescardo.github.io/DialogueTreesHeight/DialogueTreesHeight.BrouwerOrdinals.Multiplication.html
[Epsilon0]: https://github.com/martinescardo/DialogueTreesHeight/blob/master/source/DialogueTreesHeight/BrouwerOrdinals/Epsilon0.lagda
[workflow]: https://github.com/martinescardo/DialogueTreesHeight/blob/master/.github/workflows/pages.yml
[LICENSE]: https://github.com/martinescardo/DialogueTreesHeight/blob/master/LICENSE
