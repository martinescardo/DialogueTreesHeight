Heights of dialogue trees, constructively.

A classical treatment, in the wider development from which this one was
extracted, interprets the height of a dialogue tree as an ordinal in
`Ordinal 𝓤₀`. There the grafting and generic lemmas need excluded middle,
because the successor map on ordinals is not monotone without it, for which
see `succ-not-necessarily-monotone` in Ordinals.AdditionProperties.

We take the height to be a Brouwer ordinal code instead, and we equip the codes
with their syntactic order, for which the successor is monotone by
construction. The order and the addition on the codes are ordinal arithmetic
and are in the module BrouwerOrdinals.Order, which this module re-exports. We
add the height function and its three lemmas. The only assumption is function
extensionality, used in the first lemma alone.

The height of a dialogue tree `d : B ℕ` is the Brouwer code

    height (η n)   = Z
    height (β φ i) = L (λ n → S (height (φ n))),

that is, `0` at a leaf and the supremum of the heights of the subtrees raised
by one at a query node. Under the standard interpretation
`⟦_⟧₀ : B → Ordinal 𝓤₀` of Ordinals.BrouwerCodesInterpretations, this code
denotes the rank of the underlying tree branching over `ℕ`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.DialogueTrees.Constructive
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import DialogueTreesHeight.BrouwerOrdinals.Order fe public

\end{code}

The height of a dialogue tree, as a Brouwer ordinal code.

\begin{code}

height : B ℕ → 𝓑
height (η n)   = Z
height (β φ i) = L (λ n → S (height (φ n)))

\end{code}

Relabelling the leaves, which is the action
`B-functor f = kleisli-extension (η ∘ f)` of the dialogue functor, does
preserves the height, since the height ignores the values at the leaves and
depends on the branching structure alone. This is the only result that uses
function extensionality.

\begin{code}

height-relabel : (f : ℕ → ℕ) (d : B ℕ)
               → height (B-functor f d) ＝ height d
height-relabel f (η n)   = refl
height-relabel f (β φ i) =
 ap L (dfunext fe (λ j → ap S (height-relabel f (φ j))))

height-B-functor-succ : (d : B ℕ) → height (B-functor succ d) ＝ height d
height-B-functor-succ = height-relabel succ

\end{code}

Grafting. If every tree `g k` grafted at the leaves has height at most `b`,
then grafting them onto `d` by the Kleisli extension gives a tree of height at
most `b ⊕ height d`. The summand `b` is on the left, because the structure of
`d` lies above the grafted trees. The successor step is unconditional, so the
proof is constructive.

\begin{code}

height-kleisli-extension
 : (g : ℕ → B ℕ) (b : 𝓑)
 → ((k : ℕ) → height (g k) ≤ b)
 → (d : B ℕ)
 → height (kleisli-extension g d) ≤ (b ⊕ height d)
height-kleisli-extension g b ϕ (η k)   = ϕ k
height-kleisli-extension g b ϕ (β φ i) =
 ≤-L-mono (λ j → ≤-S (height-kleisli-extension g b ϕ (φ j)))

\end{code}

The generic point. Applying it adds at most one to the height.

\begin{code}

height-generic : (d : B ℕ) → height (generic d) ≤ S (height d)
height-generic (η n)   = ≤-L (λ j → ≤-S ≤-Z)
height-generic (β φ i) =
 ≤-L (λ j → ≤-S (≤-trans
                  (height-generic (φ j))
                  (≤-ℓ j (≤-refl (S (height (φ j)))))))

\end{code}
