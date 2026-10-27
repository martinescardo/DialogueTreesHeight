Finite multiples, and what absorbs them.

A bound in this development is a sum of several pieces, each of them below one
code, and what has to be shown is that the sum is still below a value that
code carries. The sum is not a multiple of the code, since addition of
ordinals does not commute and the pieces are interleaved, but it is below a
finite multiple of it, and that suffices: a value is a code times `ω^ e`, and
a finite multiple is absorbed by one successor on `e`.

The relation `x ⋖ M` says that `x` is below some finite multiple of `M`. It
holds of anything below `M`, it is closed under addition, and `⋖-⊗` turns it
into the inequality that the later proofs use.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.BrouwerOrdinals.Absorb
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import DialogueTreesHeight.BrouwerOrdinals.Order fe
 using (_≤_ ; _⊕_ ; ≤-refl ; ≤-trans ; ≤-L ; ≤-ℓ)
open import DialogueTreesHeight.BrouwerOrdinals.Multiplication fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-mono-left ; ⊗-assoc ; ⊗-left-distrib)
open import DialogueTreesHeight.BrouwerOrdinals.Epsilon0 fe
 using (ω^_ ; ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right ; ι[_]≤ω ;
        Z-left-unit ; SZ-⊗)
open import DialogueTreesHeight.BrouwerOrdinals.MultAffine fe
 using (ιn⊗ω-≤-ω)

\end{code}

A finite multiple times `ω^ e` is below `ω^ (S e)`, by induction on `e`. At
`Z` the multiple is a numeral and `ω^ (S Z)` is `ω`, at a successor the
product reassociates, and at a limit both sides are limits.

\begin{code}

ι⊗ω^ : (k : ℕ) (e : 𝓑) → (ι[ k ] ⊗ ω^ e) ≤ ω^ (S e)
ι⊗ω^ k Z     =
 transport ((Z ⊕ ι[ k ]) ≤_) ((SZ-⊗ ω) ⁻¹)
   (transport (_≤ ω) ((Z-left-unit ι[ k ]) ⁻¹) ι[ k ]≤ω)
ι⊗ω^ k (S e) =
 transport (_≤ ((ω^ (S e)) ⊗ ω))
           (⊗-assoc ι[ k ] (ω^ e) ω)
           (⊗-mono-left (ι⊗ω^ k e) ω)
ι⊗ω^ k (L f) =
 ≤-L (λ n → ≤-trans (ι⊗ω^ k (f n))
                    (⊗-mono-left (≤-ℓ n (≤-refl (ω^ (f n)))) ω))

\end{code}

A sum of numerals is a numeral.

\begin{code}

ι⊕ : (k l : ℕ) → Σ j ꞉ ℕ , (ι[ k ] ⊕ ι[ l ]) ＝ ι[ j ]
ι⊕ k zero     = k , refl
ι⊕ k (succ l) = succ (pr₁ (ι⊕ k l)) , ap S (pr₂ (ι⊕ k l))

\end{code}

Being below a finite multiple.

\begin{code}

_⋖_ : 𝓑 → 𝓑 → 𝓤₀ ̇
x ⋖ M = Σ k ꞉ ℕ , x ≤ (M ⊗ ι[ k ])

⋖-base : (M x : 𝓑) → x ≤ M → x ⋖ M
⋖-base M x p = 1 , transport (x ≤_) ((Z-left-unit M) ⁻¹) p

⋖-⊕ : (M x y : 𝓑) → x ⋖ M → y ⋖ M → (x ⊕ y) ⋖ M
⋖-⊕ M x y (k , p) (l , q) =
 pr₁ (ι⊕ k l) ,
 transport (λ z → (x ⊕ y) ≤ (M ⊗ z)) (pr₂ (ι⊕ k l))
   (transport ((x ⊕ y) ≤_)
              ((⊗-left-distrib M ι[ k ] ι[ l ]) ⁻¹)
              (≤-trans (⊕-mono-left p y)
                       (⊕-mono-right (M ⊗ ι[ k ]) q)))

\end{code}

What a finite multiple is absorbed by: one successor on an exponent.

\begin{code}

⋖-⊗ : (M x e : 𝓑) → x ⋖ M → (x ⊗ ω^ e) ≤ (M ⊗ ω^ (S e))
⋖-⊗ M x e (k , p) =
 ≤-trans (⊗-mono-left p (ω^ e))
         (transport (_≤ (M ⊗ ω^ (S e)))
                    ((⊗-assoc M ι[ k ] (ω^ e)) ⁻¹)
                    (⊗-mono-right M (ι⊗ω^ k e)))

\end{code}

A finite multiple is below the code times `ω`, which is the form in which the
exponent of a value is compared.

\begin{code}

⋖-⊗ω : (M x : 𝓑) → x ⋖ M → x ≤ (M ⊗ ω)
⋖-⊗ω M x (k , p) = ≤-trans p (⊗-mono-right M ι[ k ]≤ω)

\end{code}

A doubling is absorbed by `ω` itself.

\begin{code}

⋖-ω : (M x : 𝓑) → x ⋖ M → (x ⊗ ω) ≤ (M ⊗ ω)
⋖-ω M x (k , p) =
 ≤-trans (⊗-mono-left p ω)
         (transport (_≤ (M ⊗ ω)) ((⊗-assoc M ι[ k ] ω) ⁻¹)
                    (⊗-mono-right M (ιn⊗ω-≤-ω k)))

\end{code}
