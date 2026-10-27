The repeated argument, at every pair of widths.

The combinator `S` builds, from a datum `DF` for a map of maps and a datum
`DG` for a map, the map

    x  ↦  (the map read off DF x) applied to (DG x) ,

which uses `x` twice, once to build the datum of a map and once to build the
argument of that map. We have to prove that the result is still below a single
graded map of `x`, and `sh` is the datum of such a map.

The argument is the one for a square map, now at three independent widths
rather than one, and it is otherwise unchanged. At each output order the base
is a sum of three values at `x`, namely the head of the second action, the sum
of the second action and the head of the first, which Cascade.valSc-join puts
below one value, and the multiplier that this value carries is merged into the
exponent by `⊗-assoc` and `ω^⊗`, the exponent being the same statement one
order up. The three widths add bookkeeping: the reading takes a prefix of the
first action, so the first action has to be cut down to that prefix before the
scalar lemma applies, which is the purpose of `preRD`.

Where the argument has run out of orders, the bound is the value itself.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.BrouwerOrdinals.RectApply
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import DialogueTreesHeight.BrouwerOrdinals.Order fe
 using (_≤_ ; _⊕_ ; ≤-refl ; ≤-trans)
open import DialogueTreesHeight.BrouwerOrdinals.Multiplication fe
 using (_⊗_ ; ⊕-mono-left ; ⊗-assoc ; ⊕-increasing-left)
open import DialogueTreesHeight.BrouwerOrdinals.Epsilon0 fe
 using (ω^_ ; ω^-mono ; ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right)
open import DialogueTreesHeight.BrouwerOrdinals.MultClosure fe
 using (ω^⊗)
open import DialogueTreesHeight.BrouwerOrdinals.MoveTuple fe
 using (Tup ; tsum ; _⊑_)
open import DialogueTreesHeight.BrouwerOrdinals.Cascade fe
 using (Sc ; valSc ; ScAll< ; joinSc ; joinSc-All< ; valSc-join ;
        valSc-<-ε₀)
open import DialogueTreesHeight.BrouwerOrdinals.CascadeLevel fe
 using (tupToSc ; tupToSc-All<)
open import DialogueTreesHeight.BrouwerOrdinals.Rect fe
open import DialogueTreesHeight.BrouwerOrdinals.RectAdd fe
 using (pair＝)
open import DialogueTreesHeight.BrouwerOrdinals.RectSum fe

\end{code}

The head of an action is a cascade of the argument, namely the first component
of the datum, whatever the two widths are.

\begin{code}

hdRD : (m n : ℕ) → RD m (succ n) → Sc m
hdRD zero     n D = pr₁ D
hdRD (succ m) n D = pr₁ D

valSc-hdRD : (m n : ℕ) (D : RD m (succ n)) (x : Tup m)
           → valSc m (hdRD m n D) x ＝ pr₁ (rect m (succ n) D x)
valSc-hdRD zero     n D x = refl
valSc-hdRD (succ m) n D x = refl

hdRD-All< : (m n : ℕ) (D : RD m (succ n)) → RDAll< m (succ n) D
          → ScAll< m (hdRD m n D)
hdRD-All< zero     n D h = pr₁ h
hdRD-All< (succ m) n D h = pr₁ h

\end{code}

Cutting an action down to a prefix of its output. The datum of the cut map is
the prefix of the datum, and the two commute with the action.

\begin{code}

preRD : (m a b : ℕ) → RD m (mx a b) → RD m a
preRD m        zero     b        D = ⋆
preRD m        (succ a) zero     D = D
preRD zero     (succ a) (succ b) D = pr₁ D , preRD zero a b (pr₂ D)
preRD (succ m) (succ a) (succ b) D = pr₁ D , preRD m a b (pr₂ D)

rect-preRD : (m a b : ℕ) (D : RD m (mx a b)) (x : Tup m)
           → rect m a (preRD m a b D) x ＝ pre a b (rect m (mx a b) D x)
rect-preRD m        zero     b        D x       = refl
rect-preRD m        (succ a) zero     D x       = refl
rect-preRD zero     (succ a) (succ b) D x       =
 pair＝ refl (rect-preRD zero a b (pr₂ D) x)
rect-preRD (succ m) (succ a) (succ b) D (c , t) =
 pair＝ refl (rect-preRD m a b (pr₂ D) t)

preRD-All< : (m a b : ℕ) (D : RD m (mx a b)) → RDAll< m (mx a b) D
           → RDAll< m a (preRD m a b D)
preRD-All< m        zero     b        D h = ⋆
preRD-All< m        (succ a) zero     D h = h
preRD-All< zero     (succ a) (succ b) D h =
 pr₁ h , preRD-All< zero a b (pr₂ D) (pr₂ h)
preRD-All< (succ m) (succ a) (succ b) D h =
 pr₁ h , preRD-All< m a b (pr₂ D) (pr₂ h)

\end{code}

The scalar case: a cascade read off one action of `x`, evaluated at another
action of `x`. The three values joined are the head of the second action, the
sum of the second action and the head of the first.

\begin{code}

Jsh : (m p : ℕ) → RD (succ m) (succ (succ p)) → RD (succ m) (succ p)
    → Sc (succ m)
Jsh m p DF DG =
 joinSc (succ m)
   (joinSc (succ m) (hdRD (succ m) p DG) (sumRD (succ m) (succ p) DG))
   (hdRD (succ m) (succ p) DF)

ssh : (m p : ℕ) → RD m (succ p) → RD m p → Sc m
ssh m        zero     DF DG = hdRD m zero DF
ssh zero     (succ p) DF DG =
 valSc (succ p) (tupToSc (succ p) (rect zero (succ (succ p)) DF ⋆))
                (rect zero (succ p) DG ⋆)
ssh (succ m) (succ p) DF DG =
 pr₁ (Jsh m p DF DG) ,
 joinSc m (pr₂ (Jsh m p DF DG)) (ssh m p (pr₂ DF) (pr₂ DG))

valSc-ssh : (m p : ℕ) (DF : RD m (succ p)) (DG : RD m p) (x : Tup m)
          → valSc p (tupToSc p (rect m (succ p) DF x)) (rect m p DG x)
            ≤ valSc m (ssh m p DF DG) x
valSc-ssh m        zero     DF DG x       =
 transport (pr₁ (rect m (succ zero) DF x) ≤_)
           ((valSc-hdRD m zero DF x) ⁻¹)
           (≤-refl (pr₁ (rect m (succ zero) DF x)))
valSc-ssh zero     (succ p) DF DG ⋆       = ≤-refl _
valSc-ssh (succ m) (succ p) DF DG (a , t) =
 ≤-trans step (transport (_≤ target) ((eqA ∙ eqB) ⁻¹) last)
 where
  x : Tup (succ m)
  x = (a , t)

  s : 𝓑
  s = a ⊕ tsum m t

  u₀ : 𝓑
  u₀ = valSc (succ m) (hdRD (succ m) (succ p) DF) x

  v₀ : 𝓑
  v₀ = valSc (succ m) (hdRD (succ m) p DG) x

  V′ : Tup p
  V′ = rect m p (pr₂ DG) t

  TL : 𝓑
  TL = tsum p V′

  Jm : Sc (succ m)
  Jm = Jsh m p DF DG

  cJ : 𝓑
  cJ = pr₁ Jm

  EJ : Sc m
  EJ = pr₂ Jm

  YJ : 𝓑
  YJ = valSc m EJ t

  Z″ : 𝓑
  Z″ = valSc m (ssh m p (pr₂ DF) (pr₂ DG)) t

  target : 𝓑
  target = (s ⊕ cJ) ⊗ ω^ (valSc m (joinSc m EJ (ssh m p (pr₂ DF) (pr₂ DG))) t)

  J₁ : Sc (succ m)
  J₁ = joinSc (succ m) (hdRD (succ m) p DG) (sumRD (succ m) (succ p) DG)

  sum≤ : TL ≤ valSc (succ m) (sumRD (succ m) (succ p) DG) x
  sum≤ = ≤-trans (⊕-increasing-left v₀ TL)
                 (tsum-rect (succ m) (succ p) DG x)

  base≤ : ((v₀ ⊕ TL) ⊕ u₀) ≤ valSc (succ m) Jm x
  base≤ =
   ≤-trans (⊕-mono-left
             (≤-trans (⊕-mono-right v₀ sum≤)
                      (valSc-join (succ m) (hdRD (succ m) p DG)
                                  (sumRD (succ m) (succ p) DG) x))
             u₀)
           (valSc-join (succ m) J₁ (hdRD (succ m) (succ p) DF) x)

  X : 𝓑
  X = valSc p (tupToSc p (rect m (succ p) (pr₂ DF) t)) V′

  step : (((v₀ ⊕ TL) ⊕ u₀) ⊗ ω^ X) ≤ (valSc (succ m) Jm x ⊗ ω^ Z″)
  step = ≤-trans (⊗-mono-left base≤ (ω^ X))
                 (⊗-mono-right (valSc (succ m) Jm x)
                   (ω^-mono (valSc-ssh m p (pr₂ DF) (pr₂ DG) t)))

  eqA : (valSc (succ m) Jm x ⊗ ω^ Z″) ＝ ((s ⊕ cJ) ⊗ (ω^ YJ ⊗ ω^ Z″))
  eqA = ⊗-assoc (s ⊕ cJ) (ω^ YJ) (ω^ Z″)

  eqB : ((s ⊕ cJ) ⊗ (ω^ YJ ⊗ ω^ Z″)) ＝ ((s ⊕ cJ) ⊗ ω^ (YJ ⊕ Z″))
  eqB = ap ((s ⊕ cJ) ⊗_) (ω^⊗ YJ Z″)

  last : ((s ⊕ cJ) ⊗ ω^ (YJ ⊕ Z″)) ≤ target
  last = ⊗-mono-right (s ⊕ cJ)
                      (ω^-mono (valSc-join m EJ
                                 (ssh m p (pr₂ DF) (pr₂ DG)) t))

\end{code}

The data of the scalar bound stay below `ε₀`.

\begin{code}

ssh-All< : (m p : ℕ) (DF : RD m (succ p)) (DG : RD m p)
         → RDAll< m (succ p) DF → RDAll< m p DG → ScAll< m (ssh m p DF DG)
ssh-All< m        zero     DF DG hF hG = hdRD-All< m zero DF hF
ssh-All< zero     (succ p) DF DG hF hG =
 valSc-<-ε₀ (succ p)
   (tupToSc (succ p) (rect zero (succ (succ p)) DF ⋆))
   (rect zero (succ p) DG ⋆)
   (tupToSc-All< (succ p) (rect zero (succ (succ p)) DF ⋆)
      (rect-All< zero (succ (succ p)) DF ⋆ hF ⋆))
   (rect-All< zero (succ p) DG ⋆ hG ⋆)
ssh-All< (succ m) (succ p) DF DG hF hG =
 pr₁ hJ , joinSc-All< m (pr₂ (Jsh m p DF DG))
            (ssh m p (pr₂ DF) (pr₂ DG))
            (pr₂ hJ)
            (ssh-All< m p (pr₂ DF) (pr₂ DG) (pr₂ hF) (pr₂ hG))
 where
  hJ : ScAll< (succ m) (Jsh m p DF DG)
  hJ = joinSc-All< (succ m)
         (joinSc (succ m) (hdRD (succ m) p DG)
                          (sumRD (succ m) (succ p) DG))
         (hdRD (succ m) (succ p) DF)
         (joinSc-All< (succ m) (hdRD (succ m) p DG)
            (sumRD (succ m) (succ p) DG)
            (hdRD-All< (succ m) p DG hG)
            (sumRD-All< (succ m) (succ p) DG hG))
         (hdRD-All< (succ m) (succ p) DF hF)

\end{code}

At width zero a reading returns the datum it was read from.

\begin{code}

rdOf-zero-id : (q : ℕ) (d : Tup (succ q)) (y : Tup zero)
             → rect zero (succ q) (rdOf zero (succ q) d) y ⊑ d
rdOf-zero-id zero     d y = ≤-refl (pr₁ d) , ⋆
rdOf-zero-id (succ q) d y = ≤-refl (pr₁ d) , rdOf-zero-id q (pr₂ d) y

\end{code}

The head of the composite, which is the scalar lemma applied to the first
action cut down to the prefix that the reading uses.

\begin{code}

ssub-head : (m p q : ℕ) (DF : RD m (WD (succ p) (succ q)))
            (DG : RD m (succ p)) (x : Tup m)
          → valSc (succ p)
              (tupToSc (succ p)
                (pre (succ (succ p)) (succ q)
                  (rect m (WD (succ p) (succ q)) DF x)))
              (rect m (succ p) DG x)
            ≤ valSc m (ssh m (succ p)
                        (preRD m (succ (succ p)) (succ q) DF) DG) x
ssub-head m p q DF DG x =
 transport
   (λ u → valSc (succ p) (tupToSc (succ p) u) (rect m (succ p) DG x)
          ≤ valSc m (ssh m (succ p) DF₁ DG) x)
   (rect-preRD m (succ (succ p)) (succ q) DF x)
   (valSc-ssh m (succ p) DF₁ DG x)
 where
  DF₁ : RD m (succ (succ p))
  DF₁ = preRD m (succ (succ p)) (succ q) DF

\end{code}

The composite itself, order by order.

\begin{code}

sh : (m p q : ℕ) → RD m (WD p q) → RD m p → RD m q
sh m        p        zero     DF DG = ⋆
sh m        zero     (succ q) DF DG = DF
sh zero     (succ p) (succ q) DF DG =
 ssh zero (succ p) (preRD zero (succ (succ p)) (succ q) DF) DG ,
 sh zero p q (pr₂ DF) (pr₂ DG)
sh (succ m) (succ p) (succ q) DF DG =
 ssh (succ m) (succ p) (preRD (succ m) (succ (succ p)) (succ q) DF) DG ,
 sh m p q (pr₂ DF) (pr₂ DG)

rect-ssub : (m p q : ℕ) (DF : RD m (WD p q)) (DG : RD m p) (x : Tup m)
          → rect p q (rdOf p q (rect m (WD p q) DF x)) (rect m p DG x)
            ⊑ rect m q (sh m p q DF DG) x
rect-ssub m        p        zero     DF DG x       = ⋆
rect-ssub m        zero     (succ q) DF DG x       =
 rdOf-zero-id q (rect m (succ q) DF x) ⋆
rect-ssub zero     (succ p) (succ q) DF DG x       =
 ssub-head zero p q DF DG x ,
 rect-ssub zero p q (pr₂ DF) (pr₂ DG) x
rect-ssub (succ m) (succ p) (succ q) DF DG (a , t) =
 ssub-head (succ m) p q DF DG (a , t) ,
 rect-ssub m p q (pr₂ DF) (pr₂ DG) t

sh-All< : (m p q : ℕ) (DF : RD m (WD p q)) (DG : RD m p)
        → RDAll< m (WD p q) DF → RDAll< m p DG → RDAll< m q (sh m p q DF DG)
sh-All< m        p        zero     DF DG hF hG = ⋆
sh-All< m        zero     (succ q) DF DG hF hG = hF
sh-All< zero     (succ p) (succ q) DF DG hF hG =
 ssh-All< zero (succ p) (preRD zero (succ (succ p)) (succ q) DF) DG
   (preRD-All< zero (succ (succ p)) (succ q) DF hF) hG ,
 sh-All< zero p q (pr₂ DF) (pr₂ DG) (pr₂ hF) (pr₂ hG)
sh-All< (succ m) (succ p) (succ q) DF DG hF hG =
 ssh-All< (succ m) (succ p) (preRD (succ m) (succ (succ p)) (succ q) DF) DG
   (preRD-All< (succ m) (succ (succ p)) (succ q) DF hF) hG ,
 sh-All< m p q (pr₂ DF) (pr₂ DG) (pr₂ hF) (pr₂ hG)

\end{code}
