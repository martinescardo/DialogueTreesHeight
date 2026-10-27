The clause for the recursor, at every type.

The module Predicate supplies everything the clause for the recursor needs
except a datum for the constant itself, which has to dominate the bound on the
iterates and therefore has to be exhibited. The lemma RectOrbitAct.rorbit-act
gives the bound as an action of the context, and the datum is then built as
the module SClause builds the one for `S`. The three data are combined, in the
order in which they are bound, into one tuple; the bound on the iterates is an
action of that tuple; the translation by the count is absorbed by
RectAlgebra.rect-addνc, the code added belonging to the context as well; and
the three binders are `rect-curry`, `rect-curry` and `flatRD`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.DialogueTrees.IterClause
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import DialogueTreesHeight.BrouwerOrdinals.MoveTuple fe
 using (Tup ; _⊑_ ; ⊑-trans ; All<)
open import DialogueTreesHeight.BrouwerOrdinals.Rect fe
open import DialogueTreesHeight.BrouwerOrdinals.RectAdd fe
 using (addν)
open import DialogueTreesHeight.BrouwerOrdinals.RectAlgebra fe
 using (_⊴_ ; ⊴-trans ; addRDc ; addRDc-All< ; rect-addνc ; flatRD ;
        flatRD-⊒ ; flatRD-All<)
open import DialogueTreesHeight.BrouwerOrdinals.RectOrbitAct fe
 using (rorbitD ; rorbitD-All< ; rorbit-act)
open import DialogueTreesHeight.BrouwerOrdinals.RectCurry fe
 using (cmb ; cmb-All< ; cmb-⊴-left ; cmb-⊴-right ; curryD ;
        curryD-All< ; rect-curry)
open import DialogueTreesHeight.DialogueTrees.MajorantAll fe
 using (Maj-sup ; Maj-⊕ ; μ-Iterᵀ)
open import DialogueTreesHeight.DialogueTrees.Predicate fe
 using (wd ; Dom ; Dom-mono ; Dom-sup ; Dom-⊕)

\end{code}

The widths, and the datum.

\begin{code}

module _ (σ : type) where

 p Wφ Wν Wa n₂ n₃ : ℕ
 p  = wd σ
 Wφ = WD p p
 Wν = WD 1 p
 Wa = WD p Wν
 n₂ = mx p Wφ
 n₃ = mx 1 n₂

 DI : RD n₃ p
 DI = addRDc n₃ p (rorbitD n₃ p)

 DI₂ : RD n₂ Wν
 DI₂ = curryD 1 n₂ p DI

 DI₃ : RD Wφ Wa
 DI₃ = curryD p Wφ Wν DI₂

 dI : Tup (WD Wφ Wa)
 dI = flatRD Wφ Wa DI₃

 dI-All< : All< (WD Wφ Wa) dI
 dI-All< =
  flatRD-All< Wφ Wa DI₃
    (curryD-All< p Wφ Wν DI₂
       (curryD-All< 1 n₂ p DI
          (addRDc-All< n₃ p (rorbitD n₃ p) (rorbitD-All< n₃ p))))

\end{code}

The clause.

\begin{code}

 Iter-clause : Dom ((σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ) (μ-Iterᵀ {σ}) dI
 Iter-clause φ dφ aφ hφ a da aa ha ν dν aν hν =
  Dom-mono σ (Maj-⊕ (Maj-sup (iter φ a)) ν) (addν p D v) _ main fin
  where
   v : 𝓑
   v = pr₁ dν

   u₂ : Tup n₂
   u₂ = cmb p Wφ da dφ

   u₃ : Tup n₃
   u₃ = cmb 1 n₂ dν u₂

   Au₂ : All< n₂ u₂
   Au₂ = cmb-All< p Wφ da dφ aa aφ

   Au₃ : All< n₃ u₃
   Au₃ = cmb-All< 1 n₂ dν u₂ aν Au₂

   dν⊴ : dν ⊴ u₃
   dν⊴ = cmb-⊴-left 1 n₂ dν u₂

   da⊴ : da ⊴ u₃
   da⊴ = ⊴-trans p n₂ n₃ da u₂ u₃
           (cmb-⊴-left p Wφ da dφ) (cmb-⊴-right 1 n₂ dν u₂)

   dφ⊴ : dφ ⊴ u₃
   dφ⊴ = ⊴-trans Wφ n₂ n₃ dφ u₂ u₃
           (cmb-⊴-right p Wφ da dφ) (cmb-⊴-right 1 n₂ dν u₂)

   D : Tup p
   D = rect n₃ p (rorbitD n₃ p) u₃

   dseq : ℕ → Tup p
   dseq n = iter (rect p p (rdOf p p dφ)) da n

   dseq< : (n : ℕ) → All< p (dseq n)
   dseq< zero     = aa
   dseq< (succ n) =
    rect-All< p p (rdOf p p dφ) (dseq n) (rdOf-All< p p dφ aφ) (dseq< n)

   domseq : (n : ℕ) → Dom σ (iter φ a n) (dseq n)
   domseq zero     = ha
   domseq (succ n) = hφ (iter φ a n) (dseq n) (dseq< n) (domseq n)

   bd : (n : ℕ) → dseq n ⊑ D
   bd = rorbit-act n₃ p dφ da u₃ Au₃ dφ⊴ da⊴

   sup : Dom σ (Maj-sup (iter φ a)) D
   sup = Dom-sup σ (iter φ a) D
           (λ n → Dom-mono σ (iter φ a n) (dseq n) D (domseq n) (bd n))

   main : Dom σ (Maj-⊕ (Maj-sup (iter φ a)) ν) (addν p D v)
   main = Dom-⊕ σ (Maj-sup (iter φ a)) ν v D sup hν

   d1 : Tup Wa
   d1 = rect Wφ Wa (rdOf Wφ Wa dI) dφ

   d2 : Tup Wν
   d2 = rect p Wν (rdOf p Wν d1) da

   g3 : rect Wφ Wa DI₃ dφ ⊑ d1
   g3 = rect-⊑RD Wφ Wa DI₃ (rdOf Wφ Wa dI) (flatRD-⊒ Wφ Wa DI₃) dφ

   g2 : rect n₂ Wν DI₂ u₂ ⊑ d2
   g2 = ⊑-trans Wν _ _ _
          (rect-curry p Wφ Wν DI₂ da dφ)
          (rect-⊑RD p Wν (rdOf p Wν (rect Wφ Wa DI₃ dφ)) (rdOf p Wν d1)
             (rdOf-mono p Wν (rect Wφ Wa DI₃ dφ) d1 g3) da)

   g1 : rect n₃ p DI u₃ ⊑ rect 1 p (rdOf 1 p d2) dν
   g1 = ⊑-trans p _ _ _
          (rect-curry 1 n₂ p DI dν u₂)
          (rect-⊑RD 1 p (rdOf 1 p (rect n₂ Wν DI₂ u₂)) (rdOf 1 p d2)
             (rdOf-mono 1 p (rect n₂ Wν DI₂ u₂) d2 g2) dν)

   fin : addν p D v ⊑ rect 1 p (rdOf 1 p d2) dν
   fin = ⊑-trans p _ _ _
           (rect-addνc n₃ p (rorbitD n₃ p) u₃ v dν⊴) g1

\end{code}
