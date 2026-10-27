The entries of a graded map, summed.

Both of the remaining clauses need a bound on the sum of the entries that a
graded map produces by a single scalar cascade of the argument of the map. The
recursor needs one because a cascade reads the suffix sum of the tuple it acts
on, so that iterating a cascade requires the sum to be controlled
independently of the number of steps. The combinator `S` needs one because the
second of its two applications reads the suffix sum of the output of the
first.

The bound `sumRD` is obtained by joining the cascade of each output order,
after widening the narrower ones, using Cascade.upSc and Cascade.joinSc and
these alone. Where the input has run out of orders, the entries are constants
and their sum is a constant.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.BrouwerOrdinals.RectSum
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import DialogueTreesHeight.BrouwerOrdinals.Order fe
 using (_≤_ ; _⊕_ ; ≤-Z ; ≤-trans)
open import DialogueTreesHeight.BrouwerOrdinals.Epsilon0 fe
 using (⊕-mono-right ; ⊕-<-ε₀)
open import DialogueTreesHeight.BrouwerOrdinals.MoveTuple fe
 using (Tup ; tsum)
open import DialogueTreesHeight.BrouwerOrdinals.Cascade fe
 using (Sc ; valSc ; ScAll< ; zeroSc ; zeroSc-All< ; upSc ; upSc-All< ;
        joinSc ; joinSc-All< ; valSc-up ; valSc-join)
open import DialogueTreesHeight.BrouwerOrdinals.Rect fe

\end{code}

\begin{code}

sumRD : (p q : ℕ) → RD p q → Sc p
sumRD p        zero     D         = zeroSc p
sumRD zero     (succ q) (c , D) = c ⊕ sumRD zero q D
sumRD (succ p) (succ q) (E , D) =
 joinSc (succ p) E (upSc p (sumRD p q D))

tsum-rect : (p q : ℕ) (D : RD p q) (x : Tup p)
          → tsum q (rect p q D x) ≤ valSc p (sumRD p q D) x
tsum-rect p        zero     D         x       = ≤-Z
tsum-rect zero     (succ q) (c , D) x       =
 ⊕-mono-right c (tsum-rect zero q D x)
tsum-rect (succ p) (succ q) (E , D) (a , t) =
 ≤-trans (⊕-mono-right (valSc (succ p) E (a , t))
            (≤-trans (tsum-rect p q D t)
                     (valSc-up p (sumRD p q D) a t)))
         (valSc-join (succ p) E (upSc p (sumRD p q D)) (a , t))

sumRD-All< : (p q : ℕ) (D : RD p q) → RDAll< p q D
           → ScAll< p (sumRD p q D)
sumRD-All< p        zero     D         h        = zeroSc-All< p
sumRD-All< zero     (succ q) (c , D) (h , h′) =
 ⊕-<-ε₀ c (sumRD zero q D) h (sumRD-All< zero q D h′)
sumRD-All< (succ p) (succ q) (E , D) (h , h′) =
 joinSc-All< (succ p) E (upSc p (sumRD p q D)) h
   (upSc-All< p (sumRD p q D) (sumRD-All< p q D h′))

\end{code}
