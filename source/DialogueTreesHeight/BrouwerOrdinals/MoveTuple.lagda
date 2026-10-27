Graded tuples of ordinal data.

The datum attached to a majorant is a tuple: a constant, an exponent, the
exponent of that exponent, and so on. The length of the tuple is the type
level, and the grading matters. An entry of grade `i` may be moved by an entry
of grade `i` or higher, and by those alone, because an exponent that grew with
the constant below it would exceed `ε₀` under iteration, the iterates of
`x ↦ ω^ x` from `1` having supremum `ε₀`.

A tuple is written with its entry of grade `0` first, so that the tail of a
tuple is the tuple of the higher grades. We fix here the tuples themselves,
their componentwise order, the property of having every entry below `ε₀`, and
the sum of the entries, against which a bound on a whole tuple is stated. The
maps that act on tuples, and the bound on iterating such a map, are in the
modules Rect and RectOrbitAct.

Everything here concerns Brouwer codes alone. The hereditary predicate over
the types of System T is built on it.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.BrouwerOrdinals.MoveTuple
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import DialogueTreesHeight.BrouwerOrdinals.Order fe
 using (_≤_ ; _⊕_ ; ≤-Z ; ≤-refl ; ≤-trans)
open import DialogueTreesHeight.BrouwerOrdinals.Multiplication fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-mono-left)
open import DialogueTreesHeight.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ⊗-mono-right ; ⊕-mono-right ; ⊕-<-ε₀ ; Z-left-unit ;
        ι[_]≤ω ; Z<ε₀)

\end{code}

Tuples of codes and tuples of moves, graded with grade `0` first.

\begin{code}

Tup : ℕ → 𝓤₀ ̇
Tup zero     = 𝟙 {𝓤₀}
Tup (succ n) = 𝓑 × Tup n

tsum : (n : ℕ) → Tup n → 𝓑
tsum zero     _       = Z
tsum (succ n) (a , t) = a ⊕ tsum n t

\end{code}

The componentwise order, and the property of having all entries below `ε₀`.

\begin{code}

_⊑_ : {n : ℕ} → Tup n → Tup n → 𝓤₀ ̇
_⊑_ {zero}   _       _       = 𝟙 {𝓤₀}
_⊑_ {succ n} (a , t) (b , u) = (a ≤ b) × (t ⊑ u)

⊑-refl : (n : ℕ) (t : Tup n) → t ⊑ t
⊑-refl zero     t       = ⋆
⊑-refl (succ n) (a , t) = ≤-refl a , ⊑-refl n t

⊑-trans : (n : ℕ) (t u v : Tup n) → t ⊑ u → u ⊑ v → t ⊑ v
⊑-trans zero     t u v p q = ⋆
⊑-trans (succ n) (a , t) (b , u) (c , v) (p , p′) (q , q′) =
 ≤-trans p q , ⊑-trans n t u v p′ q′

All< : (n : ℕ) → Tup n → 𝓤₀ ̇
All< zero     _       = 𝟙 {𝓤₀}
All< (succ n) (a , t) = (a < ε₀) × All< n t

tsum-mono : (n : ℕ) (t u : Tup n) → t ⊑ u → tsum n t ≤ tsum n u
tsum-mono zero     t       u       p       = ≤-Z
tsum-mono (succ n) (a , t) (b , u) (p , q) =
 ≤-trans (⊕-mono-left p (tsum n t))
         (⊕-mono-right b (tsum-mono n t u q))

tsum-<-ε₀ : (n : ℕ) (t : Tup n) → All< n t → tsum n t < ε₀
tsum-<-ε₀ zero     t       p       = Z<ε₀
tsum-<-ε₀ (succ n) (a , t) (p , q) =
 ⊕-<-ε₀ a (tsum n t) p (tsum-<-ε₀ n t q)

\end{code}

Doubling a code costs one factor of `ω`, which is how two bounds added
together are brought below a single one.

\begin{code}

dup-ω : (X : 𝓑) → (X ⊕ X) ≤ (X ⊗ ω)
dup-ω X =
 ≤-trans (transport ((X ⊕ X) ≤_) ((ap (_⊕ X) (Z-left-unit X)) ⁻¹)
                    (≤-refl (X ⊕ X)))
         (⊗-mono-right X (ι[ 2 ]≤ω))

\end{code}
