A scalar cascade read as a tuple, and domination of cascade data.

The datum of a scalar cascade of width `j` consists of `j + 1` ordinals, which
is a tuple of width `j + 1`, and we turn the two readings into each other. A
functional one level up acts on the datum of a cascade by acting on that
tuple, so the conversion is what allows a cascade to be carried as a datum by
the level above it.

Domination of cascade data is componentwise, and a cascade dominating another
has the larger value at every tuple, which is the form in which the bounds use
it.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.BrouwerOrdinals.CascadeLevel
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import DialogueTreesHeight.BrouwerOrdinals.Order fe
 using (_≤_ ; _⊕_ ; ≤-trans)
open import DialogueTreesHeight.BrouwerOrdinals.Epsilon0 fe
 using (ω^_ ; ω^-mono ; ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right)
open import DialogueTreesHeight.BrouwerOrdinals.MoveTuple fe
 using (Tup ; tsum ; _⊑_ ; All<)
open import DialogueTreesHeight.BrouwerOrdinals.Cascade fe

\end{code}

Domination of data, and that it dominates values.

\begin{code}

_⊑Sc_ : {k : ℕ} → Sc k → Sc k → 𝓤₀ ̇
_⊑Sc_ {zero}   c       c′        = c ≤ c′
_⊑Sc_ {succ k} (c , E) (c′ , E′) = (c ≤ c′) × (E ⊑Sc E′)

valSc-⊑ : (k : ℕ) (E E′ : Sc k) → E ⊑Sc E′ → (t : Tup k)
        → valSc k E t ≤ valSc k E′ t
valSc-⊑ zero     c       c′        p       t       = p
valSc-⊑ (succ k) (c , E) (c′ , E′) (p , q) (a , t) =
 ≤-trans (⊗-mono-left (⊕-mono-right (a ⊕ tsum k t) p) (ω^ (valSc k E t)))
         (⊗-mono-right ((a ⊕ tsum k t) ⊕ c′)
                       (ω^-mono (valSc-⊑ k E E′ q t)))

\end{code}

A scalar cascade of width `j` and a tuple of width `j + 1` hold the same
ordinals.

\begin{code}

scToTup : (j : ℕ) → Sc j → Tup (succ j)
scToTup zero     c       = c , ⋆
scToTup (succ j) (c , E) = c , scToTup j E

tupToSc : (j : ℕ) → Tup (succ j) → Sc j
tupToSc zero     (a , t) = a
tupToSc (succ j) (a , t) = a , tupToSc j t

scToTup-⊑ : (j : ℕ) (E : Sc j) (u : Tup (succ j))
          → scToTup j E ⊑ u → E ⊑Sc tupToSc j u
scToTup-⊑ zero     c       (a , t) (p , q) = p
scToTup-⊑ (succ j) (c , E) (a , u) (p , q) = p , scToTup-⊑ j E u q

scToTup-All< : (j : ℕ) (E : Sc j) → ScAll< j E → All< (succ j) (scToTup j E)
scToTup-All< zero     c       p        = p , ⋆
scToTup-All< (succ j) (c , E) (c< , p) = c< , scToTup-All< j E p

tupToSc-All< : (j : ℕ) (u : Tup (succ j)) → All< (succ j) u
             → ScAll< j (tupToSc j u)
tupToSc-All< zero     (a , t) (a< , p) = a<
tupToSc-All< (succ j) (a , u) (a< , p) = a< , tupToSc-All< j u p

\end{code}
