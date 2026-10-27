The main theorems, restated.

A theorem is worth exactly its statement, so we restate here, independently,
the four results of the development: the upper bound of the module
Fundamental, and the lower bound, the cofinality and the least bound of the
module Sharpness. Each restatement has the abbreviations unfolded, the strict
order as a successor on the left and `ε₀` as the limit of the tower, and is
inhabited by the same proof term as the original. We also check that the
order is not degenerate at the bottom, that the type the theorems quantify
over is inhabited, and that the tower is the sequence of iterated powers of
`ω` that the statements are about, and we name the types of `dialogue-tree`
and of `height`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.DialogueTrees.Main (fe : Fun-Ext) where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT
open import EffectfulForcing.MFPSAndVariations.MFPS-XXIX using (dialogue-tree)
open import EffectfulForcing.MFPSAndVariations.Dialogue using (B)
open import DialogueTreesHeight.BrouwerOrdinals.Order fe
 using (_≤_)
open import DialogueTreesHeight.BrouwerOrdinals.Multiplication fe
 using (ω)
open import DialogueTreesHeight.BrouwerOrdinals.Epsilon0 fe
 using (ε₀ ; tower ; ω^_)
open import DialogueTreesHeight.DialogueTrees.Constructive fe
 using (height)
open import DialogueTreesHeight.DialogueTrees.Fundamental fe
 using (dialogue-tree-height-<-ε₀)
open import DialogueTreesHeight.DialogueTrees.Sharpness fe
 using (tower-term ; tower-attained ; heights-cofinal ; ε₀-least)

\end{code}

The upper bound, written out independently: the height of the dialogue tree
of every term is strictly below `ε₀`.

\begin{code}

restated : (t : T ((ι ⇒ ι) ⇒ ι)) → (S (height (dialogue-tree t))) ≤ ε₀
restated = dialogue-tree-height-<-ε₀

\end{code}

The order is not degenerate at the bottom, and the type the theorem
quantifies over is inhabited, so that the theorem is not vacuous.

\begin{code}

no-S≤Z : S Z ≤ Z → 𝟘 {𝓤₀}
no-S≤Z ()

example : T ((ι ⇒ ι) ⇒ ι)
example = K · Zero

witness : (S (height (dialogue-tree example))) ≤ ε₀
witness = dialogue-tree-height-<-ε₀ example

\end{code}

A dialogue tree is a tree of queries, and its height is a Brouwer code.

\begin{code}

tree-type : T ((ι ⇒ ι) ⇒ ι) → B ℕ
tree-type = dialogue-tree

height-type : B ℕ → 𝓑
height-type = height

\end{code}

The tower is the sequence of iterated powers of `ω`, and `ε₀` is its limit.

\begin{code}

tower-base : tower 0 ＝ ω
tower-base = refl

tower-step : (n : ℕ) → tower (succ n) ＝ ω^ (tower n)
tower-step n = refl

ε₀-is-limit-of-tower : ε₀ ＝ L tower
ε₀-is-limit-of-tower = refl

\end{code}

The lower bound: for every `n`, the `n`-th level of the tower is below the
height of the dialogue tree of the `n`-th term.

\begin{code}

attained : (n : ℕ) → tower n ≤ height (dialogue-tree (tower-term n))
attained = tower-attained

\end{code}

Cofinality, with the strict order unfolded: every code strictly below the
limit of the tower is below the height of the dialogue tree of some term.

\begin{code}

cofinal : (a : 𝓑)
        → S a ≤ L tower
        → Σ t ꞉ T ((ι ⇒ ι) ⇒ ι) , a ≤ height (dialogue-tree t)
cofinal = heights-cofinal

\end{code}

The least bound, with `ε₀` unfolded: a code above the height of every
dialogue tree is above the limit of the tower.

\begin{code}

least : (b : 𝓑)
      → ((t : T ((ι ⇒ ι) ⇒ ι)) → height (dialogue-tree t) ≤ b)
      → L tower ≤ b
least = ε₀-least

\end{code}

The terms the lower bound is about are terms of the type the upper bound
quantifies over.

\begin{code}

term-type : ℕ → T ((ι ⇒ ι) ⇒ ι)
term-type = tower-term

\end{code}
