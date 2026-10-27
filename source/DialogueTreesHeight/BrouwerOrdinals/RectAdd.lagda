Adding a code to a datum, at every width.

The majorant of the recursor is the supremum of the iterates translated by the
height of the count argument, and the translation passes under the argument at
every type, so a datum has to absorb `⊕ ν`. A translation alone cannot absorb
it, since that would be the fold `b ⊗ m ⊕ d ≤ (b ⊕ d) ⊗ m`, which fails for a
limit multiplier. We pay for it instead by adding the code at order zero and
one successor at every order above, which is the definition of `addν`. The
reason is the same at every order: a value with its own multiplier is above
both itself enlarged and the code added, so the sum of the two is below the
value doubled, and a doubling costs one successor on the order above.

The reading `rdOf` has to commute with the adjustment, so that adjusting a
datum and then reading it as a map gives the adjusted map. It does, because
both operations act componentwise on the tuple, and the three commutations are
those of `pre`, of `tupToSc` and of `rdOf` with the successor.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.BrouwerOrdinals.RectAdd
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import DialogueTreesHeight.BrouwerOrdinals.Order fe
 using (_≤_ ; _⊕_ ; ≤-refl ; ≤-trans)
open import DialogueTreesHeight.BrouwerOrdinals.Multiplication fe
 using (ω ; _⊗_ ; ⊕-mono-left ; ⊗-assoc ; ⊕-increasing-left)
open import DialogueTreesHeight.BrouwerOrdinals.Epsilon0 fe
 using (ω^_ ; ω^-mono ; one-≤-ω^ ; ⊗-mono-left ; ⊗-mono-right ;
        ⊕-mono-right ; ⊕-increasing-right ; x-≤-x⊗)
open import DialogueTreesHeight.BrouwerOrdinals.MoveTuple fe
 using (Tup ; tsum ; _⊑_ ; dup-ω)
open import DialogueTreesHeight.BrouwerOrdinals.Cascade fe
 using (Sc ; valSc ; sucSc ; valSc-suc)
open import DialogueTreesHeight.BrouwerOrdinals.CascadeLevel fe
 using (tupToSc)
open import DialogueTreesHeight.BrouwerOrdinals.Rect fe

\end{code}

The adjustment, on tuples and on the data of a map.

\begin{code}

sucTup : (n : ℕ) → Tup n → Tup n
sucTup zero     t       = ⋆
sucTup (succ n) (a , t) = S a , sucTup n t

addν : (n : ℕ) → Tup n → 𝓑 → Tup n
addν zero     t       v = ⋆
addν (succ n) (a , t) v = (a ⊕ v) , sucTup n t

sucRD : (p q : ℕ) → RD p q → RD p q
sucRD p        zero     D       = ⋆
sucRD zero     (succ q) (c , D) = S c , sucRD zero q D
sucRD (succ p) (succ q) (E , D) = sucSc (succ p) E , sucRD p q D

addRD : (p q : ℕ) → RD p q → 𝓑 → RD p q
addRD p        zero     D       v = ⋆
addRD zero     (succ q) (c , D) v = (c ⊕ v) , sucRD zero q D
addRD (succ p) (succ q) (E , D) v =
 ((pr₁ E ⊕ v) , sucSc p (pr₂ E)) , sucRD p q D

\end{code}

A code added outside a cascade is absorbed by adding it to the translation of
the cascade and taking one successor above.

\begin{code}

valSc-fold : (k : ℕ) (c : 𝓑) (E : Sc k) (t : Tup (succ k)) (v : 𝓑)
           → (valSc (succ k) (c , E) t ⊕ v)
             ≤ valSc (succ k) ((c ⊕ v) , sucSc k E) t
valSc-fold k c E (a , u) v =
 ≤-trans (⊕-mono-left t1 v)
  (≤-trans (⊕-mono-right Q t2)
   (≤-trans (transport ((Q ⊕ Q) ≤_) eqQ (dup-ω Q))
            (⊗-mono-right (s ⊕ (c ⊕ v))
                          (ω^-mono (valSc-suc k E u)))))
 where
  s : 𝓑
  s = a ⊕ tsum k u

  X : 𝓑
  X = valSc k E u

  Q : 𝓑
  Q = (s ⊕ (c ⊕ v)) ⊗ ω^ X

  t1 : ((s ⊕ c) ⊗ ω^ X) ≤ Q
  t1 = ⊗-mono-left (⊕-mono-right s (⊕-increasing-right c v)) (ω^ X)

  t2 : v ≤ Q
  t2 = ≤-trans (⊕-increasing-left c v)
       (≤-trans (⊕-increasing-left s (c ⊕ v))
                (x-≤-x⊗ (s ⊕ (c ⊕ v)) (ω^ X) (one-≤-ω^ X)))

  eqQ : (Q ⊗ ω) ＝ ((s ⊕ (c ⊕ v)) ⊗ ω^ (S X))
  eqQ = ⊗-assoc (s ⊕ (c ⊕ v)) (ω^ X) ω

\end{code}

The adjustment passes through the action.

\begin{code}

rect-sucRD : (p q : ℕ) (D : RD p q) (x : Tup p)
           → sucTup q (rect p q D x) ⊑ rect p q (sucRD p q D) x
rect-sucRD p        zero     D         x       = ⋆
rect-sucRD zero     (succ q) (c , D) x       =
 ≤-refl (S c) , rect-sucRD zero q D x
rect-sucRD (succ p) (succ q) (E , D) (a , t) =
 valSc-suc (succ p) E (a , t) , rect-sucRD p q D t

rect-addRD : (p q : ℕ) (D : RD p q) (x : Tup p) (v : 𝓑)
           → addν q (rect p q D x) v ⊑ rect p q (addRD p q D v) x
rect-addRD p        zero     D         x       v = ⋆
rect-addRD zero     (succ q) (c , D) x       v =
 ≤-refl (c ⊕ v) , rect-sucRD zero q D x
rect-addRD (succ p) (succ q) (E , D) (a , t) v =
 valSc-fold p (pr₁ E) (pr₂ E) (a , t) v , rect-sucRD p q D t

\end{code}

The reading commutes with the adjustment.

\begin{code}

pair＝ : {A B : 𝓤₀ ̇ } {a a′ : A} {b b′ : B}
      → a ＝ a′ → b ＝ b′ → (a , b) ＝ (a′ , b′)
pair＝ refl refl = refl

pre-sucTup : (a b : ℕ) (t : Tup (mx a b))
           → pre a b (sucTup (mx a b) t) ＝ sucTup a (pre a b t)
pre-sucTup zero     b        t       = refl
pre-sucTup (succ a) zero     t       = refl
pre-sucTup (succ a) (succ b) (x , t) =
 ap (S x ,_) (pre-sucTup a b t)

tupToSc-sucTup : (j : ℕ) (t : Tup (succ j))
               → tupToSc j (sucTup (succ j) t) ＝ sucSc j (tupToSc j t)
tupToSc-sucTup zero     (a , t) = refl
tupToSc-sucTup (succ j) (a , t) = ap (S a ,_) (tupToSc-sucTup j t)

rdOf-sucTup : (p q : ℕ) (d : Tup (WD p q))
            → rdOf p q (sucTup (WD p q) d) ＝ sucRD p q (rdOf p q d)
rdOf-sucTup p        zero            d = refl
rdOf-sucTup zero     (succ zero)     d = refl
rdOf-sucTup zero     (succ (succ q)) d =
 ap (S (pr₁ d) ,_) (rdOf-sucTup zero (succ q) (pr₂ d))
rdOf-sucTup (succ p) (succ q)        d =
 pair＝
   (ap (tupToSc (succ p)) (pre-sucTup (succ (succ p)) (succ q) d)
    ∙ tupToSc-sucTup (succ p) (pre (succ (succ p)) (succ q) d))
   (rdOf-sucTup p q (pr₂ d))

pre-addν : (a b : ℕ) (t : Tup (mx a b)) (v : 𝓑)
         → pre a b (addν (mx a b) t v) ＝ addν a (pre a b t) v
pre-addν zero     b        t       v = refl
pre-addν (succ a) zero     t       v = refl
pre-addν (succ a) (succ b) (x , t) v = ap ((x ⊕ v) ,_) (pre-sucTup a b t)

tupToSc-addν : (j : ℕ) (w : Tup (succ (succ j))) (v : 𝓑)
             → tupToSc (succ j) (addν (succ (succ j)) w v)
               ＝ ((pr₁ w ⊕ v) , sucSc j (pr₂ (tupToSc (succ j) w)))
tupToSc-addν j (x , u) v = ap ((x ⊕ v) ,_) (tupToSc-sucTup j u)

rdOf-addν : (p q : ℕ) (d : Tup (WD p q)) (v : 𝓑)
          → rdOf p q (addν (WD p q) d v) ＝ addRD p q (rdOf p q d) v
rdOf-addν p        zero            d v = refl
rdOf-addν zero     (succ zero)     d v = refl
rdOf-addν zero     (succ (succ q)) d v =
 ap ((pr₁ d ⊕ v) ,_) (rdOf-sucTup zero (succ q) (pr₂ d))
rdOf-addν (succ p) (succ q)        d v =
 pair＝
   (ap (tupToSc (succ p)) (pre-addν (succ (succ p)) (succ q) d v)
    ∙ tupToSc-addν p (pre (succ (succ p)) (succ q) d) v)
   (rdOf-sucTup p q (pr₂ d))

\end{code}

Putting the two together: adjusting a datum and then acting is above acting
and then adjusting.

\begin{code}

rect-addν : (p q : ℕ) (d : Tup (WD p q)) (x : Tup p) (v : 𝓑)
          → addν q (rect p q (rdOf p q d) x) v
            ⊑ rect p q (rdOf p q (addν (WD p q) d v)) x
rect-addν p q d x v =
 transport (λ D → addν q (rect p q (rdOf p q d) x) v ⊑ rect p q D x)
           ((rdOf-addν p q d v) ⁻¹)
           (rect-addRD p q (rdOf p q d) x v)

\end{code}
