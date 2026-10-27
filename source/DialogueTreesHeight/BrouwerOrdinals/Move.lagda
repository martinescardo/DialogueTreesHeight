Moves on ordinal data, and their closure under iteration.

The constant and the exponent of the data of a ground transform are each
moved, by the functional that iterates it, through a map of one fixed shape,

    a ↦ (a ⊕ t) ⊗ ω^ s ,

the affine form with the constant inside the product, which composes without
right distributivity. We call such a map a move, given by a pair of ordinals
`(t , s)` with `s` positive and both below `ε₀`, acting on a code `a` by
`img mv a = (a ⊕ t) ⊗ ω^ s`, and we prove the closure fact that the recursor
argument uses at every type level: iterating a move stays below a single move,
with the exponent multiplied by `ω`, so that `(t , s)` becomes `(t , s ⊗ ω)`.
The bound is sharp, in that it keeps the exponent within its tower level
rather than passing to the next one, and it makes the moves closed under their
own iteration.

A move takes a code below `ε₀` to a code below `ε₀`. The moves therefore form
a small algebra, closed under iteration and with values below `ε₀`, and the
hereditary predicate for the dialogue-height majorant is, at each level, a
tuple of moves acting on the data of the level below.

A move carries the validity of its multiplier `ω^ s` as a field, rather than
deriving it from `s ≥ 1`. The inequality `ι[2] ⊗ ω^ s ≤ ω^ s` does not reduce
for an arbitrary positive `s`, because at a limit exponent the approximants
need not be positive, so the absorption has to come from the way the exponent
was built. Every move constructed here supplies it from `dbl-ω^`, and so does
every move the predicates build.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.BrouwerOrdinals.Move
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import DialogueTreesHeight.BrouwerOrdinals.Order fe
 using (_≤_ ; _⊕_ ; ≤-trans ; ≤-L-upper-bound)
open import DialogueTreesHeight.BrouwerOrdinals.Multiplication fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-mono-left)
open import DialogueTreesHeight.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ω^_ ; ω^-mono ; ω^-<-ε₀ ; one-≤-ω^ ; ⊗-mono-left ;
        ⊗-mono-right ; ι[_]≤ω ; x-≤-x⊗ ; ω<ε₀)
open import DialogueTreesHeight.BrouwerOrdinals.MultClosure fe
 using (⊗-<-ε₀)
open import DialogueTreesHeight.BrouwerOrdinals.MultAffine fe
 using (ω-pos ; dbl-ω^ ; orbit-inv ; pw-ω^)

\end{code}

A valid multiplier is positive, absorbs doubling, and is below `ε₀`. A move
asserts this of `ω^ ms`.

\begin{code}

ValidMult : 𝓑 → 𝓤₀ ̇
ValidMult M = (S Z ≤ M) × ((ι[ 2 ] ⊗ M) ≤ M) × (M < ε₀)

\end{code}

A move consists of the translation `mt`, the exponent `ms`, which is positive,
the validity of the multiplier `ω^ ms`, and the two bounds below `ε₀`.

\begin{code}

record Move : 𝓤₀ ̇ where
 constructor move
 field
  mt     : 𝓑
  ms     : 𝓑
  mt<    : mt < ε₀
  ms+    : S Z ≤ ms
  ms<    : ms < ε₀
  mvalid : ValidMult (ω^ ms)

open Move public

\end{code}

The action of a move on a code is monotone, and preserves being below `ε₀`.

\begin{code}

img : Move → 𝓑 → 𝓑
img mv a = (a ⊕ mt mv) ⊗ ω^ (ms mv)

img-mono : (mv : Move) {a a′ : 𝓑} → a ≤ a′ → img mv a ≤ img mv a′
img-mono mv p = ⊗-mono-left (⊕-mono-left p (mt mv)) (ω^ (ms mv))

\end{code}

Iterating a move from `a` stays below the single move with the same
translation and with the exponent multiplied by `ω`.

\begin{code}

orbit : Move → Move
orbit mv =
 move (mt mv) (ms mv ⊗ ω) (mt< mv)
      (≤-trans (ms+ mv) (x-≤-x⊗ (ms mv) ω ω-pos))
      sω<
      (one-≤-ω^ (ms mv ⊗ ω) , dbl-ω^ (ms mv) (ms+ mv)
      , ω^-<-ε₀ (ms mv ⊗ ω) sω<)
 where
  sω< : (ms mv ⊗ ω) < ε₀
  sω< = ⊗-<-ε₀ (ms mv) ω (ms< mv) ω<ε₀

move-orbit : (mv : Move) (a : 𝓑) (k : ℕ)
           → iter (img mv) a k ≤ img (orbit mv) a
move-orbit mv a k =
 ≤-trans (orbit-inv (ω^ (ms mv)) (one-≤-ω^ (ms mv))
                    (pr₁ (pr₂ (mvalid mv))) a (mt mv) k)
         (⊗-mono-right (a ⊕ mt mv)
           (≤-trans (pw-ω^ (ms mv) k)
                    (ω^-mono (⊗-mono-right (ms mv)
                                           (≤-L-upper-bound ι[_] k)))))

\end{code}

The recurrence in the form that every level uses: a family of codes that
starts below `a₀` and grows by at most one move per step is uniformly below
the iterated move applied to `a₀`.

\begin{code}

move-orbit-rec : (mv : Move) (a : ℕ → 𝓑) (a₀ : 𝓑)
               → a 0 ≤ a₀
               → ((k : ℕ) → a (succ k) ≤ img mv (a k))
               → (k : ℕ) → a k ≤ img (orbit mv) a₀
move-orbit-rec mv a a₀ base step k =
 ≤-trans (dom k) (move-orbit mv a₀ k)
 where
  dom : (j : ℕ) → a j ≤ iter (img mv) a₀ j
  dom zero     = base
  dom (succ j) = ≤-trans (step j) (img-mono mv (dom j))

\end{code}

These lemmas are stated for codes alone, so the same arithmetic serves at
ground type, at the second order and above.

A level of the hierarchy builds the moves of the level below from ordinals it
has just computed, such as bounds on iterates and sums, for which it has
positivity and a bound below `ε₀`, while the absorption of doubling by the
multiplier has still to be supplied. Padding the exponent by `⊗ ω` supplies
the absorption, since `dbl-ω^` asks only that `s` be positive, and padding
only enlarges the bound.

Every move the hierarchy builds is built in this way, so the padding always
supplies the validity field, and the general inequality `ι[2] ⊗ ω^ s ≤ ω^ s`
for an arbitrary positive `s`, which no argument available here proves, can be
dispensed with.

\begin{code}

padMove : (t s : 𝓑) → t < ε₀ → S Z ≤ s → s < ε₀ → Move
padMove t s t< s+ s< =
 move t (s ⊗ ω) t<
      (≤-trans s+ (x-≤-x⊗ s ω ω-pos))
      sω<
      (one-≤-ω^ (s ⊗ ω) , dbl-ω^ s s+ , ω^-<-ε₀ (s ⊗ ω) sω<)
 where
  sω< : (s ⊗ ω) < ε₀
  sω< = ⊗-<-ε₀ s ω s< ω<ε₀

\end{code}
