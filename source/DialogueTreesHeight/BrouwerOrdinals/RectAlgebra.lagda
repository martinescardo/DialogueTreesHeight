The algebra of graded maps: zero, join, widening, and flattening.

Four constructions on the data of a graded map, each with the one fact about
it that the development uses: the zero map; the join of two maps, which
dominates both, by Cascade.joinSc at every order; the widening of a map to a
wider output, which agrees with the given map on the prefix; and the
flattening of a map into a tuple it can be read back out of, which performs
the half of currying that binds a variable absent from the body.

Flattening needs the slotwise addition of a short tuple into a longer one,
since a cascade and the tuple produced by the recursion have to fit into the
same slots.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.BrouwerOrdinals.RectAlgebra
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import DialogueTreesHeight.BrouwerOrdinals.Order fe
 using (_≤_ ; _⊕_ ; ≤-refl ; ≤-trans ; ≤-S)
open import DialogueTreesHeight.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; S-increasing ; ⊕-increasing-right ; ⊕-<-ε₀ ;
        ⊕-mono-right ; S-<-ε₀ ; Z<ε₀)
open import DialogueTreesHeight.BrouwerOrdinals.Multiplication fe
 using (⊕-increasing-left)
open import DialogueTreesHeight.BrouwerOrdinals.MoveTuple fe
 using (Tup ; _⊑_ ; ⊑-refl ; All<)
open import DialogueTreesHeight.BrouwerOrdinals.Cascade fe
 using (Sc ; valSc ; sucSc ; sucSc-All< ; joinSc ; joinSc-All< ;
        valSc-join ; zeroSc ; zeroSc-All< ; valSc-increasing)
open import DialogueTreesHeight.BrouwerOrdinals.CascadeLevel fe
 using (_⊑Sc_ ; scToTup ; scToTup-⊑ ; scToTup-All<)
open import DialogueTreesHeight.BrouwerOrdinals.Rect fe
open import DialogueTreesHeight.BrouwerOrdinals.RectAdd fe
 using (pair＝ ; addν ; sucRD ; rect-sucRD)

\end{code}

Reflexivity and transitivity of the two orders on data.

\begin{code}

⊑Sc-trans : (k : ℕ) (E F G : Sc k) → E ⊑Sc F → F ⊑Sc G → E ⊑Sc G
⊑Sc-trans zero     E       F       G       p       q       = ≤-trans p q
⊑Sc-trans (succ k) (c , E) (d , F) (e , G) (p , p′) (q , q′) =
 ≤-trans p q , ⊑Sc-trans k E F G p′ q′

⊑RD-trans : (p q : ℕ) (D D′ D″ : RD p q)
          → D ⊑RD D′ → D′ ⊑RD D″ → D ⊑RD D″
⊑RD-trans p        zero     D         D′         D″          h h′ = ⋆
⊑RD-trans zero     (succ q) (c , D) (c′ , D′) (c″ , D″) (h , p) (h′ , p′) =
 ≤-trans h h′ , ⊑RD-trans zero q D D′ D″ p p′
⊑RD-trans (succ p) (succ q) (E , D) (E′ , D′) (E″ , D″) (h , r) (h′ , r′) =
 ⊑Sc-trans (succ p) E E′ E″ h h′ , ⊑RD-trans p q D D′ D″ r r′

\end{code}

A cascade is below its successor and below either join.

\begin{code}

sucSc-⊒ : (k : ℕ) (E : Sc k) → E ⊑Sc sucSc k E
sucSc-⊒ zero     c       = S-increasing c
sucSc-⊒ (succ k) (c , E) = S-increasing c , sucSc-⊒ k E

joinSc-left : (k : ℕ) (E F : Sc k) → E ⊑Sc joinSc k E F
joinSc-left zero     c       d       = ⊕-increasing-right c d
joinSc-left (succ k) (c , E) (d , F) =
 ⊕-increasing-right c d ,
 ⊑Sc-trans k E (joinSc k E F) (sucSc k (joinSc k E F))
   (joinSc-left k E F) (sucSc-⊒ k (joinSc k E F))

joinSc-right : (k : ℕ) (E F : Sc k) → F ⊑Sc joinSc k E F
joinSc-right zero     c       d       = ⊕-increasing-left c d
joinSc-right (succ k) (c , E) (d , F) =
 ⊕-increasing-left c d ,
 ⊑Sc-trans k F (joinSc k E F) (sucSc k (joinSc k E F))
   (joinSc-right k E F) (sucSc-⊒ k (joinSc k E F))

\end{code}

The zero tuple and the zero map.

\begin{code}

zeroTup : (n : ℕ) → Tup n
zeroTup zero     = ⋆
zeroTup (succ n) = Z , zeroTup n

zeroTup-All< : (n : ℕ) → All< n (zeroTup n)
zeroTup-All< zero     = ⋆
zeroTup-All< (succ n) = Z<ε₀ , zeroTup-All< n

zeroRD : (n k : ℕ) → RD n k
zeroRD n        zero     = ⋆
zeroRD zero     (succ k) = Z , zeroRD zero k
zeroRD (succ n) (succ k) = zeroSc (succ n) , zeroRD n k

zeroRD-All< : (n k : ℕ) → RDAll< n k (zeroRD n k)
zeroRD-All< n        zero     = ⋆
zeroRD-All< zero     (succ k) = Z<ε₀ , zeroRD-All< zero k
zeroRD-All< (succ n) (succ k) = zeroSc-All< (succ n) , zeroRD-All< n k

\end{code}

The join of two maps.

\begin{code}

joinRD : (n k : ℕ) → RD n k → RD n k → RD n k
joinRD n        zero     D         D′         = ⋆
joinRD zero     (succ k) (c , D) (c′ , D′) = (c ⊕ c′) , joinRD zero k D D′
joinRD (succ n) (succ k) (E , D) (E′ , D′) =
 joinSc (succ n) E E′ , joinRD n k D D′

joinRD-left : (n k : ℕ) (D D′ : RD n k) → D ⊑RD joinRD n k D D′
joinRD-left n        zero     D         D′         = ⋆
joinRD-left zero     (succ k) (c , D) (c′ , D′) =
 ⊕-increasing-right c c′ , joinRD-left zero k D D′
joinRD-left (succ n) (succ k) (E , D) (E′ , D′) =
 joinSc-left (succ n) E E′ , joinRD-left n k D D′

joinRD-right : (n k : ℕ) (D D′ : RD n k) → D′ ⊑RD joinRD n k D D′
joinRD-right n        zero     D         D′         = ⋆
joinRD-right zero     (succ k) (c , D) (c′ , D′) =
 ⊕-increasing-left c c′ , joinRD-right zero k D D′
joinRD-right (succ n) (succ k) (E , D) (E′ , D′) =
 joinSc-right (succ n) E E′ , joinRD-right n k D D′

joinRD-All< : (n k : ℕ) (D D′ : RD n k) → RDAll< n k D → RDAll< n k D′
            → RDAll< n k (joinRD n k D D′)
joinRD-All< n        zero     D         D′         h        h′        = ⋆
joinRD-All< zero     (succ k) (c , D) (c′ , D′) (h , p) (h′ , p′) =
 ⊕-<-ε₀ c c′ h h′ , joinRD-All< zero k D D′ p p′
joinRD-All< (succ n) (succ k) (E , D) (E′ , D′) (h , p) (h′ , p′) =
 joinSc-All< (succ n) E E′ h h′ , joinRD-All< n k D D′ p p′

\end{code}

Widening the output of a map, which leaves the prefix unchanged.

\begin{code}

padRD : (n a b : ℕ) → RD n a → RD n (mx a b)
padRD n        zero     b        D       = zeroRD n b
padRD n        (succ a) zero     D       = D
padRD zero     (succ a) (succ b) (c , D) = c , padRD zero a b D
padRD (succ n) (succ a) (succ b) (E , D) = E , padRD n a b D

rect-padRD : (n a b : ℕ) (D : RD n a) (x : Tup n)
           → pre a b (rect n (mx a b) (padRD n a b D) x) ＝ rect n a D x
rect-padRD n        zero     b        D       x       = refl
rect-padRD n        (succ a) zero     D       x       = refl
rect-padRD zero     (succ a) (succ b) (c , D) x       =
 pair＝ refl (rect-padRD zero a b D x)
rect-padRD (succ n) (succ a) (succ b) (E , D) (c , t) =
 pair＝ refl (rect-padRD n a b D t)

padRD-All< : (n a b : ℕ) (D : RD n a) → RDAll< n a D
           → RDAll< n (mx a b) (padRD n a b D)
padRD-All< n        zero     b        D       h = zeroRD-All< n b
padRD-All< n        (succ a) zero     D       h = h
padRD-All< zero     (succ a) (succ b) (c , D) h =
 pr₁ h , padRD-All< zero a b D (pr₂ h)
padRD-All< (succ n) (succ a) (succ b) (E , D) h =
 pr₁ h , padRD-All< n a b D (pr₂ h)

\end{code}

Adding a short tuple into a longer one, slotwise.

\begin{code}

taddTup : (n : ℕ) → Tup n → Tup n → Tup n
taddTup zero     t       u       = ⋆
taddTup (succ n) (a , t) (b , u) = (a ⊕ b) , taddTup n t u

taddTup-left : (n : ℕ) (t u : Tup n) → t ⊑ taddTup n t u
taddTup-left zero     t       u       = ⋆
taddTup-left (succ n) (a , t) (b , u) =
 ⊕-increasing-right a b , taddTup-left n t u

taddTup-right : (n : ℕ) (t u : Tup n) → u ⊑ taddTup n t u
taddTup-right zero     t       u       = ⋆
taddTup-right (succ n) (a , t) (b , u) =
 ⊕-increasing-left a b , taddTup-right n t u

taddTup-All< : (n : ℕ) (t u : Tup n) → All< n t → All< n u
             → All< n (taddTup n t u)
taddTup-All< zero     t       u       ht hu = ⋆
taddTup-All< (succ n) (a , t) (b , u) ht hu =
 ⊕-<-ε₀ a b (pr₁ ht) (pr₁ hu) , taddTup-All< n t u (pr₂ ht) (pr₂ hu)

padd : (a b : ℕ) → Tup a → Tup (mx a b) → Tup (mx a b)
padd zero     b        t       u        = u
padd (succ a) zero     t       u        = taddTup (succ a) t u
padd (succ a) (succ b) (c , t) (u₀ , u) = (c ⊕ u₀) , padd a b t u

padd-right : (a b : ℕ) (t : Tup a) (u : Tup (mx a b)) → u ⊑ padd a b t u
padd-right zero     b        t       u        = ⊑-refl (mx zero b) u
padd-right (succ a) zero     t       u        = taddTup-right (succ a) t u
padd-right (succ a) (succ b) (c , t) (u₀ , u) =
 ⊕-increasing-left c u₀ , padd-right a b t u

padd-left : (a b : ℕ) (t : Tup a) (u : Tup (mx a b))
          → t ⊑ pre a b (padd a b t u)
padd-left zero     b        t       u        = ⋆
padd-left (succ a) zero     t       u        = taddTup-left (succ a) t u
padd-left (succ a) (succ b) (c , t) (u₀ , u) =
 ⊕-increasing-right c u₀ , padd-left a b t u

padd-All< : (a b : ℕ) (t : Tup a) (u : Tup (mx a b)) → All< a t
          → All< (mx a b) u → All< (mx a b) (padd a b t u)
padd-All< zero     b        t       u        ht hu = hu
padd-All< (succ a) zero     t       u        ht hu =
 taddTup-All< (succ a) t u ht hu
padd-All< (succ a) (succ b) (c , t) (u₀ , u) ht hu =
 ⊕-<-ε₀ c u₀ (pr₁ ht) (pr₁ hu) , padd-All< a b t u (pr₂ ht) (pr₂ hu)

\end{code}

Flattening a map into a tuple it can be read back out of. At each order the
entries of the cascade are added into the slots that the recursion has already
claimed, which is the reason for the addition above.

\begin{code}

flatRD : (p q : ℕ) → RD p q → Tup (WD p q)
flatRD p        zero            D       = zeroTup (succ p)
flatRD zero     (succ zero)     (c , D) = c , ⋆
flatRD zero     (succ (succ q)) (c , D) = c , flatRD zero (succ q) D
flatRD (succ p) (succ q)        (E , D) =
 pr₁ E , padd (succ p) q (scToTup p (pr₂ E)) (flatRD p q D)

flatRD-⊒ : (p q : ℕ) (D : RD p q) → D ⊑RD rdOf p q (flatRD p q D)
flatRD-⊒ p        zero            D       = ⋆
flatRD-⊒ zero     (succ zero)     (c , D) = ≤-refl c , ⋆
flatRD-⊒ zero     (succ (succ q)) (c , D) =
 ≤-refl c , flatRD-⊒ zero (succ q) D
flatRD-⊒ (succ p) (succ q)        (E , D) =
 scToTup-⊑ (succ p) E
   (pr₁ E , pre (succ p) q (padd (succ p) q (scToTup p (pr₂ E))
                                 (flatRD p q D)))
   (≤-refl (pr₁ E) ,
    padd-left (succ p) q (scToTup p (pr₂ E)) (flatRD p q D)) ,
 ⊑RD-trans p q D (rdOf p q (flatRD p q D))
   (rdOf p q (padd (succ p) q (scToTup p (pr₂ E)) (flatRD p q D)))
   (flatRD-⊒ p q D)
   (rdOf-mono p q (flatRD p q D)
      (padd (succ p) q (scToTup p (pr₂ E)) (flatRD p q D))
      (padd-right (succ p) q (scToTup p (pr₂ E)) (flatRD p q D)))

flatRD-All< : (p q : ℕ) (D : RD p q) → RDAll< p q D
            → All< (WD p q) (flatRD p q D)
flatRD-All< p        zero            D       h = zeroTup-All< (succ p)
flatRD-All< zero     (succ zero)     (c , D) h = pr₁ h , ⋆
flatRD-All< zero     (succ (succ q)) (c , D) h =
 pr₁ h , flatRD-All< zero (succ q) D (pr₂ h)
flatRD-All< (succ p) (succ q)        (E , D) h =
 pr₁ (pr₁ h) ,
 padd-All< (succ p) q (scToTup p (pr₂ E)) (flatRD p q D)
   (scToTup-All< p (pr₂ E) (pr₂ (pr₁ h)))
   (flatRD-All< p q D (pr₂ h))

\end{code}

A tuple is contained in a wider one when it is below it slot by slot as far as
it reaches. The zero map then dominates it, because at each order a value is
above the entry it is applied to. This is how the datum of a variable is
recovered from the datum of the whole context.

\begin{code}

_⊴_ : {k n : ℕ} → Tup k → Tup n → 𝓤₀ ̇
_⊴_ {zero}   {n}      t       u       = 𝟙 {𝓤₀}
_⊴_ {succ k} {zero}   t       u       = 𝟘 {𝓤₀}
_⊴_ {succ k} {succ n} (a , t) (b , u) = (a ≤ b) × (t ⊴ u)

⊴-refl : (n : ℕ) (u : Tup n) → u ⊴ u
⊴-refl zero     u       = ⋆
⊴-refl (succ n) (a , u) = ≤-refl a , ⊴-refl n u

⊴-trans : (k n j : ℕ) (t : Tup k) (u : Tup n) (v : Tup j)
        → t ⊴ u → u ⊴ v → t ⊴ v
⊴-trans zero     n        j        t       u       v       h h′ = ⋆
⊴-trans (succ k) zero     j        t       u       v       h h′ = 𝟘-elim h
⊴-trans (succ k) (succ n) zero     t       u       v       h h′ = 𝟘-elim h′
⊴-trans (succ k) (succ n) (succ j) (a , t) (b , u) (c , v) (h , p) (h′ , p′) =
 ≤-trans h h′ , ⊴-trans k n j t u v p p′

≤-<-ε₀ : (a b : 𝓑) → a ≤ b → b < ε₀ → a < ε₀
≤-<-ε₀ a b h h′ = ≤-trans (≤-S h) h′

⊴-All< : (k n : ℕ) (t : Tup k) (u : Tup n) → t ⊴ u → All< n u → All< k t
⊴-All< zero     n        t       u       h       hu = ⋆
⊴-All< (succ k) zero     t       u       h       hu = 𝟘-elim h
⊴-All< (succ k) (succ n) (a , t) (b , u) (h , p) hu =
 ≤-<-ε₀ a b h (pr₁ hu) , ⊴-All< k n t u p (pr₂ hu)

pre-⊴ : (a b : ℕ) (t : Tup (mx a b)) → pre a b t ⊴ t
pre-⊴ zero     b        t       = ⋆
pre-⊴ (succ a) zero     t       = ⊴-refl (succ a) t
pre-⊴ (succ a) (succ b) (c , t) = ≤-refl c , pre-⊴ a b t

rect-⊴ : (n k : ℕ) (u : Tup n) (t : Tup k) → t ⊴ u
       → t ⊑ rect n k (zeroRD n k) u
rect-⊴ n        zero     u       t       h       = ⋆
rect-⊴ zero     (succ k) u       t       h       = 𝟘-elim h
rect-⊴ (succ n) (succ k) (b , u) (a , t) (h , p) =
 ≤-trans h (valSc-increasing n Z (zeroSc n) b u) , rect-⊴ n k u t p

\end{code}

Adding the first entry of the context at order zero and a successor above,
which is what the translation of the recursor by the count asks of a datum.
The code added belongs to the context, so it is absorbed by joining the
cascade of order zero with the zero cascade, whose value is above the entry it
is applied to.

\begin{code}

sucRD-All< : (p q : ℕ) (D : RD p q) → RDAll< p q D
           → RDAll< p q (sucRD p q D)
sucRD-All< p        zero     D       h = ⋆
sucRD-All< zero     (succ q) (c , D) h =
 S-<-ε₀ c (pr₁ h) , sucRD-All< zero q D (pr₂ h)
sucRD-All< (succ p) (succ q) (E , D) h =
 sucSc-All< (succ p) E (pr₁ h) , sucRD-All< p q D (pr₂ h)

addRDc : (n p : ℕ) → RD n p → RD n p
addRDc n        zero     D       = ⋆
addRDc zero     (succ p) (c , D) = c , sucRD zero p D
addRDc (succ n) (succ p) (E , D) =
 joinSc (succ n) E (zeroSc (succ n)) , sucRD n p D

rect-addνc : (n p : ℕ) (D : RD n p) (u : Tup n) (v : 𝓑)
           → (v , ⋆) ⊴ u
           → addν p (rect n p D u) v ⊑ rect n p (addRDc n p D) u
rect-addνc n        zero     D       u        v h       = ⋆
rect-addνc zero     (succ p) (c , D) u        v h       = 𝟘-elim h
rect-addνc (succ n) (succ p) (E , D) (u₀ , u) v (h , _) =
 ≤-trans (⊕-mono-right (valSc (succ n) E (u₀ , u))
            (≤-trans h (valSc-increasing n Z (zeroSc n) u₀ u)))
         (valSc-join (succ n) E (zeroSc (succ n)) (u₀ , u)) ,
 rect-sucRD n p D u

addRDc-All< : (n p : ℕ) (D : RD n p) → RDAll< n p D
            → RDAll< n p (addRDc n p D)
addRDc-All< n        zero     D       h = ⋆
addRDc-All< zero     (succ p) (c , D) h =
 pr₁ h , sucRD-All< zero p D (pr₂ h)
addRDc-All< (succ n) (succ p) (E , D) h =
 joinSc-All< (succ n) E (zeroSc (succ n)) (pr₁ h) (zeroSc-All< (succ n)) ,
 sucRD-All< n p D (pr₂ h)

\end{code}
