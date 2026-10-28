Terms and trees of prescribed height.

The theorem bounds the height of the dialogue tree of a term of System T by
`ε₀`. We complement it here from two sides.

First with terms at the bottom of the scale: a term whose tree is a leaf, a
term whose tree is a single query, and a term whose tree has height `ω`, which
is `tower 0`, the first approximant of `ε₀`. The terms are written with the
combinators, so that the interpretation computes and each dialogue tree is
obtained by `refl`. Writing `I` for the identity combinator, the three terms
are `λ f → 0`, `λ f → f 0` and `λ f → iter f (f 0) (f 0)`, the last asking the
oracle at `0` and then asking it as many further times as the answer
prescribes.

Then with trees: every Brouwer code is the height of a dialogue tree, and the
tree is read off the code. Each approximant `tower n` of `ε₀` is therefore the
height of a dialogue tree, and so is `ε₀` itself, and the tree of height at
least `ε₀` is the dialogue tree of no term of System T. The bound of the
theorem is a statement about the terms, the trees themselves reaching every
height.

The order on Brouwer codes is inductively generated, so a lower bound on a
limit code asks for a uniform witness: `L f ≤ b` holds when every `f n` is
below `b`, and `a ≤ L f` holds when `a` is below a single `f n`. A numeral is
below one branch of a tree, which is what makes the lower bound `ω ≤ height`
available for the third term, by induction on the numeral. A limit code needs
a branch of its own at every index, so a term realising `tower n` for
`n ≥ 1` uses recursion at higher types. The module Sharpness constructs
such terms from Church encodings of the approximants, with the lower bound
proved by a parametricity argument.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.DialogueTrees.Examples
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.CombinatoryT
open import EffectfulForcing.MFPSAndVariations.MFPS-XXIX
 using (dialogue-tree)
open import DialogueTreesHeight.BrouwerOrdinals.Order fe
 using (_≤_ ; _⊕_ ; ≤-Z ; ≤-S ; ≤-ℓ ; ≤-L ; ≤-refl ; ≤-trans)
open import DialogueTreesHeight.BrouwerOrdinals.Multiplication fe
 using (ι[_] ; ω ; ⊕-mono-left)
open import DialogueTreesHeight.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; S-increasing ; tower)
open import DialogueTreesHeight.DialogueTrees.Fundamental fe
 using (dialogue-tree-height-<-ε₀)
open import DialogueTreesHeight.DialogueTrees.Constructive fe
 using (height ; height-generic)

\end{code}

The three terms.

\begin{code}

I : {σ : type} → T (σ ⇒ σ)
I = S · K · (K {_} {ι})

leaf-term : T ((ι ⇒ ι) ⇒ ι)
leaf-term = K · Zero

query-term : T ((ι ⇒ ι) ⇒ ι)
query-term = S · I · (K · Zero)

iterated-term : T ((ι ⇒ ι) ⇒ ι)
iterated-term = S · (S · (S · (K · Iter) · I) · query-term) · query-term

\end{code}

Their dialogue trees, each by computation. The third asks the oracle at `0`
and grafts, onto the leaf `j` of that query, the tree of `j` further queries.

\begin{code}

leaf-tree : dialogue-tree leaf-term ＝ η 0
leaf-tree = refl

query-tree : dialogue-tree query-term ＝ β η 0
query-tree = refl

iterated-tree : dialogue-tree iterated-term
              ＝ β (λ j → iter generic (β η 0) j) 0
iterated-tree = refl

\end{code}

The first two heights. The tree of a leaf has height `Z`, and the tree of one
query has height `S Z` in the sense that each bound holds.

\begin{code}

leaf-height : height (dialogue-tree leaf-term) ＝ Z
leaf-height = refl

query-height-≤ : height (dialogue-tree query-term) ≤ S Z
query-height-≤ = ≤-L (λ n → ≤-S ≤-Z)

query-height-≥ : S Z ≤ height (dialogue-tree query-term)
query-height-≥ = ≤-ℓ 0 (≤-S ≤-Z)

\end{code}

One application of the oracle raises the height of a numeral by one. The proof
is by induction on the numeral, and the numeral is carried through a single
branch at each step, which is where the natural order is used.

\begin{code}

ι-generic : (k : ℕ) (d : B ℕ)
          → ι[ k ] ≤ height d
          → ι[ succ k ] ≤ height (generic d)
ι-generic zero     (η n)   p              = ≤-ℓ 0 (≤-S ≤-Z)
ι-generic zero     (β φ i) p              = ≤-ℓ 0 (≤-S ≤-Z)
ι-generic (succ k) (β φ i) (≤-ℓ n (≤-S q)) =
 ≤-ℓ n (≤-S (ι-generic k (φ n) q))

ι-iter : (k : ℕ) (d : B ℕ) → ι[ k ] ≤ height (iter generic d k)
ι-iter zero     d = ≤-Z
ι-iter (succ k) d = ι-generic k (iter generic d k) (ι-iter k d)

\end{code}

In the other direction, `k` applications of the oracle raise the height by at
most `k`.

\begin{code}

iter-generic-≤ : (k : ℕ) (d : B ℕ)
               → height (iter generic d k) ≤ (height d ⊕ ι[ k ])
iter-generic-≤ zero     d = ≤-refl (height d)
iter-generic-≤ (succ k) d =
 ≤-trans (height-generic (iter generic d k))
         (≤-S (iter-generic-≤ k d))

one⊕ι : (k : ℕ) → (S Z ⊕ ι[ k ]) ＝ ι[ succ k ]
one⊕ι zero     = refl
one⊕ι (succ k) = ap S (one⊕ι k)

\end{code}

The third term therefore has height `ω`, the first approximant of `ε₀`, again
in the sense that each bound holds.

\begin{code}

iterated-height-≥ : tower 0 ≤ height (dialogue-tree iterated-term)
iterated-height-≥ =
 ≤-L (λ j → ≤-ℓ j (≤-trans (ι-iter j (β η 0))
                           (S-increasing (height (iter generic (β η 0) j)))))

iterated-height-≤ : height (dialogue-tree iterated-term) ≤ tower 0
iterated-height-≤ = ≤-L (λ j → ≤-ℓ (succ (succ j)) (step j))
 where
  base≤ : height (β η 0) ≤ S Z
  base≤ = ≤-L (λ n → ≤-S ≤-Z)

  step : (j : ℕ) → S (height (iter generic (β η 0) j)) ≤ ι[ succ (succ j) ]
  step j = ≤-S (≤-trans (iter-generic-≤ j (β η 0))
                        (transport ((height (β η 0) ⊕ ι[ j ]) ≤_)
                                   (one⊕ι j)
                                   (⊕-mono-left base≤ ι[ j ])))

\end{code}

The tree read off a code. A successor becomes a query whose subtrees are all
the tree of the predecessor, and a limit becomes a query whose `n`-th subtree
is the tree of the `n`-th approximant.

\begin{code}

tree-of : 𝓑 → B ℕ
tree-of Z     = η 0
tree-of (S a) = β (λ _ → tree-of a) 0
tree-of (L f) = β (λ n → tree-of (f n)) 0

code-≤-height : (a : 𝓑) → a ≤ height (tree-of a)
code-≤-height Z     = ≤-Z
code-≤-height (S a) = ≤-ℓ 0 (≤-S (code-≤-height a))
code-≤-height (L f) =
 ≤-L (λ n → ≤-ℓ n (≤-trans (code-≤-height (f n))
                           (S-increasing (height (tree-of (f n))))))

\end{code}

In particular there is, for each `n`, a dialogue tree whose height is at least
`tower n`, the `n`-th approximant of `ε₀`, and a dialogue tree whose height is
at least `ε₀` itself.

\begin{code}

approximant : (n : ℕ) → tower n ≤ height (tree-of (tower n))
approximant n = code-≤-height (tower n)

epsilon₀ : ε₀ ≤ height (tree-of ε₀)
epsilon₀ = code-≤-height ε₀

\end{code}

The last of these is beyond the reach of System T. Each code is strictly below
its own successor, by induction on the code, the limit case using that a
member of a limit is below the limit.

\begin{code}

S-irrefl : (a : 𝓑) → S a ≤ a → 𝟘 {𝓤₀}
S-irrefl (S a) (≤-S p)   = S-irrefl a p
S-irrefl (L f) (≤-ℓ n p) =
 S-irrefl (f n) (≤-trans (≤-S (≤-ℓ n (≤-refl (f n)))) p)

\end{code}

So no term of System T has `tree-of ε₀` for its dialogue tree, while for each
`n` the approximant `tower n` is the height of a dialogue tree. The theorem
bounds the terms, and the trees themselves are unbounded.

\begin{code}

no-term-of-height-ε₀ : (t : T ((ι ⇒ ι) ⇒ ι))
                     → dialogue-tree t ＝ tree-of ε₀
                     → 𝟘
no-term-of-height-ε₀ t e =
 S-irrefl ε₀ (≤-trans (≤-S (transport (λ - → ε₀ ≤ height -) (e ⁻¹) epsilon₀))
                      (dialogue-tree-height-<-ε₀ t))

\end{code}
