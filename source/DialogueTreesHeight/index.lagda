The dialogue-tree height of a term of System T of type `(ι ⇒ ι) ⇒ ι` is below
`ε₀`, and `ε₀` is the least bound.

This is the full proof, which includes only what is used to prove the above.

The ordinals are the Brouwer codes of Ordinals.BrouwerCodes, with their
syntactic order. Every module is checked with `--safe` and `--without-K`, and
the only hypothesis is function extensionality, taken as the module parameter
`fe` and used at the limit case of each arithmetic law proved by induction,
among them associativity of the product.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DialogueTreesHeight.index where

import DialogueTreesHeight.BrouwerOrdinals.Order
import DialogueTreesHeight.BrouwerOrdinals.Multiplication
import DialogueTreesHeight.BrouwerOrdinals.Epsilon0
import DialogueTreesHeight.BrouwerOrdinals.MultClosure
import DialogueTreesHeight.BrouwerOrdinals.MultAffine
import DialogueTreesHeight.BrouwerOrdinals.Absorb
import DialogueTreesHeight.BrouwerOrdinals.Move
import DialogueTreesHeight.BrouwerOrdinals.MoveTuple
import DialogueTreesHeight.BrouwerOrdinals.Cascade
import DialogueTreesHeight.BrouwerOrdinals.CascadeLevel
import DialogueTreesHeight.BrouwerOrdinals.Rect
import DialogueTreesHeight.BrouwerOrdinals.RectAdd
import DialogueTreesHeight.BrouwerOrdinals.RectAlgebra
import DialogueTreesHeight.BrouwerOrdinals.RectSum
import DialogueTreesHeight.BrouwerOrdinals.RectApply
import DialogueTreesHeight.BrouwerOrdinals.RectCurry
import DialogueTreesHeight.BrouwerOrdinals.RectOrbitAct
import DialogueTreesHeight.DialogueTrees.Constructive
import DialogueTreesHeight.DialogueTrees.Majorant
import DialogueTreesHeight.DialogueTrees.MajorantAll
import DialogueTreesHeight.DialogueTrees.Predicate
import DialogueTreesHeight.DialogueTrees.IterClause
import DialogueTreesHeight.DialogueTrees.SClause
import DialogueTreesHeight.DialogueTrees.Fundamental
import DialogueTreesHeight.DialogueTrees.Examples
import DialogueTreesHeight.DialogueTrees.Sharpness
import DialogueTreesHeight.DialogueTrees.Main

\end{code}

An outline of the proof.

The ordinal arithmetic comes first and concerns Brouwer codes alone. The
module Order defines their syntactic order, for which the successor is
monotone outright, and their addition. The module Multiplication adds the
numerals, the limit `ω`, the product, and the laws by which the bounds are
moved. The module Epsilon0 adds base-`ω` exponentiation, the tower whose
supremum is `ε₀`, and the closure of `ε₀` under addition, the successor and
exponentiation, and the module MultClosure adds its closure under
multiplication.

The dialogue side comes next. The module Constructive defines the height of a
dialogue tree as a Brouwer code and proves the three lemmas about relabelling,
grafting and the generic point. The module Majorant sets up a height-indexed
logical relation and gives every combinator but the recursor a majorant. The
module MajorantAll equips the majorants with a hereditary supremum and a
hereditary translation, proves the Kleisli bound by induction on the type, and
so gives the recursor a majorant at every type. Its fundamental theorem bounds
the height of a closed term by its majorant, which reduces the conjecture to
the ordinal statement `μᵀ t < ε₀`.

The bound on the majorant occupies the remaining modules. A majorant is
bounded by a tuple of ordinals graded by order, a constant, an exponent, the
exponent of that exponent, and so on, and the discipline throughout is that an
entry is raised only by entries of its own order or higher, which is the
property that the iterates of `x ↦ ω^ x` violate. The module MultAffine
iterates a body with a limit multiplier. The module Move isolates the maps
`a ↦ (a ⊕ t) ⊗ ω^ s` and bounds their iterates, and the module MoveTuple fixes
the graded tuples. The module Cascade lets the exponent of such a map be a map
of the same kind one order up, which is what the combinator `S` requires, and
the module CascadeLevel reads such a map as a tuple, so that the level above
can carry it.

The module Rect assembles these into the graded maps between tuples of any two
widths, with the module RectAdd for the translation that the recursor applies
after a supremum, the module RectSum for the sum of the entries of a map, and
the module RectAlgebra for the zero map, the join, the widening and the
flattening. Three facts about these maps carry the two remaining clauses. The
module RectApply bounds a map applied to its own argument twice. The module
RectCurry binds a variable by currying, the module Absorb supplying the
absorption of a finite multiple into an exponent. The module RectOrbitAct
bounds the iterates of a square map by an action of the context, which is what
makes the bound a datum rather than an existential tuple.

The module Predicate defines the hereditary predicate `Dom` over the types of
System T, graded by the order of a type, proves that it is monotone, closed
under suprema and closed under the translation, and gives the clauses for the
constants that follow from those properties alone. The module SClause gives the
clause for `S` and the module IterClause the clause for the recursor. The
module Fundamental puts the clauses together by induction on terms, concludes
`μᵀ t < ε₀`, and derives the theorem. The module Examples exhibits terms at the
bottom of the scale, among them one whose dialogue tree has height `ω`, the
first approximant of `ε₀`, and reads off every Brouwer code a dialogue tree of
at least that height, so that each approximant of `ε₀` is the height of a
dialogue tree while the trees of System T terms stay below `ε₀`. The module
Sharpness runs Church encodings of the approximants against the oracle and
shows that, for each `n`, a term of System T attains the height `tower n`, so
that the heights of the dialogue trees are cofinal in `ε₀` and the bound of the
theorem is the least one. The module Main restates the theorem and these three
results independently, with the abbreviations unfolded, and checks that the
same proof terms inhabit the restatements.

References

The dialogue-tree interpretation of System T and the conjecture proved here
are those of [5], where the trees are inductive; they are Church encoded
within System T in [6]. The hereditary assignment of ordinals to terms, type
by type, follows the method of Howard [2], and the bound `ε₀` is the ordinal
of Gentzen's consistency proof of arithmetic [1], of which a modern account
is [4]. The terms of the module Sharpness Church encode ordinals instead,
after Coquand, Hancock and Setzer [3], through the module
Ordinals.ChurchEncoding.

The bound is due to Xiao and Sun [7], who compute from each term a level of
the tower bounding the height of its tree, and this development is an
alternative proof of it. Their ordinals are the classical ones, their
formalisation assuming excluded middle for the propositions of the second
universe along with univalence, propositional truncation and set
replacement, whereas the ordinals here are Brouwer codes with their
syntactic order and function extensionality is the only assumption. They
leave open whether the heights are cofinal in `ε₀`, which the module
Sharpness settles, so that `ε₀` is the least bound.

[1] G. Gentzen. Die Widerspruchsfreiheit der reinen Zahlentheorie.
    Mathematische Annalen 112 (1936) 493-565. English translation in
    M. E. Szabo (ed.), The Collected Papers of Gerhard Gentzen,
    North-Holland, 1969.

[2] W. A. Howard. Assignment of ordinals to terms for primitive recursive
    functionals of finite type. In A. Kino, J. Myhill and R. E. Vesley
    (eds.), Intuitionism and Proof Theory (Buffalo 1968), North-Holland,
    1970, 443-458.

[3] T. Coquand, P. Hancock and A. Setzer. Ordinals in type theory.
    Invited talk at CSL 1997.
    https://www.cse.chalmers.se/~coquand/ordinal.pdf

[4] W. Pohlers. Proof Theory: The First Step into Impredicativity.
    Universitext, Springer, 2009.

[5] M. H. Escardó. Continuity of Gödel's system T definable functionals
    via effectful forcing. MFPS XXIX. Electronic Notes in Theoretical
    Computer Science 298 (2013).
    https://doi.org/10.1016/j.entcs.2013.09.010

[6] M. H. Escardó, B. da Rocha Paiva, V. Rahli and A. Tosun. Internal
    effectful forcing in System T. FSCD 2025. Leibniz International
    Proceedings in Informatics 337, 19:1-19:17.
    https://doi.org/10.4230/LIPIcs.FSCD.2025.19

[7] M. Xiao and Y. Sun. An explicit ordinal bound for System T dialogue
    trees. Preprint, arXiv:2609.20369, 2026.
    https://arxiv.org/abs/2609.20369

We now import the TypeTopology modules which are not used but are mentioned
in the prose discussion.

\begin{code}

import Ordinals.AdditionProperties
import Ordinals.BrouwerCodesInterpretations
import Ordinals.ChurchEncoding

\end{code}
