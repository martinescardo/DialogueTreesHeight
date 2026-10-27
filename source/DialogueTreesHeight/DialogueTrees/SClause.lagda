The clause for `S`, at every triple of types.

A datum for `S` at `ρ = σ = τ = ι` can be exhibited by hand. At general widths
the datum is built, rather than designed, from three constructions about
graded maps alone: an action of a tuple applied to another action of the same
tuple is an action of that tuple, which is RectApply.rect-ssub; an action of a
tuple that combines two others is read back as an action of one of them whose
output acts on the other, which is RectCurry.rect-curry; and the datum of a
variable is below the datum of the context containing it, which is
RectAlgebra.rect-⊴.

The proof is then the one that a reader of `λ f g a → f a (g a)` would write.
The three data arrive one at a time and are combined, in the order in which
they are bound, into one tuple. The body is two applications over that one
tuple, which is `rect-ssub` twice, and the three binders are `rect-curry`,
`rect-curry` and RectAlgebra.flatRD, the last being currying with an empty
context. The datum of `S` itself depends only on the three widths.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.DialogueTrees.SClause
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT
open import DialogueTreesHeight.BrouwerOrdinals.MoveTuple fe
 using (Tup ; _⊑_ ; ⊑-trans ; All<)
open import DialogueTreesHeight.BrouwerOrdinals.Rect fe
open import DialogueTreesHeight.BrouwerOrdinals.RectAlgebra fe
 using (_⊴_ ; ⊴-trans ; zeroRD ; zeroRD-All< ; rect-⊴ ; flatRD ;
        flatRD-⊒ ; flatRD-All<)
open import DialogueTreesHeight.BrouwerOrdinals.RectApply fe
 using (sh ; sh-All< ; rect-ssub)
open import DialogueTreesHeight.BrouwerOrdinals.RectCurry fe
 using (cmb ; cmb-All< ; cmb-⊴-left ; cmb-⊴-right ; curryD ;
        curryD-All< ; rect-curry)
open import DialogueTreesHeight.DialogueTrees.Majorant fe
 using (μ-S)
open import DialogueTreesHeight.DialogueTrees.Predicate fe
 using (wd ; Dom ; Dom-mono)

\end{code}

The widths concerned, and the datum.

\begin{code}

module _ (ρ σ τ : type) where

 m p q : ℕ
 m = wd ρ
 p = wd σ
 q = wd τ

 WF WG W2 n₂ n₃ : ℕ
 WF = WD m (WD p q)
 WG = WD m p
 W2 = WD WG (WD m q)
 n₂ = mx WG WF
 n₃ = mx m n₂

 De : RD n₃ m
 De = zeroRD n₃ m

 DF : RD n₃ WF
 DF = zeroRD n₃ WF

 DG : RD n₃ WG
 DG = zeroRD n₃ WG

 A₁ : RD n₃ (WD p q)
 A₁ = sh n₃ m (WD p q) DF De

 A₂ : RD n₃ p
 A₂ = sh n₃ m p DG De

 B : RD n₃ q
 B = sh n₃ p q A₁ A₂

 B₂ : RD n₂ (WD m q)
 B₂ = curryD m n₂ q B

 B₃ : RD WF W2
 B₃ = curryD WG WF (WD m q) B₂

 dS : Tup (WD WF W2)
 dS = flatRD WF W2 B₃

\end{code}

Its entries stay below `ε₀`.

\begin{code}

 A₁-All< : RDAll< n₃ (WD p q) A₁
 A₁-All< = sh-All< n₃ m (WD p q) DF De
             (zeroRD-All< n₃ WF) (zeroRD-All< n₃ m)

 A₂-All< : RDAll< n₃ p A₂
 A₂-All< = sh-All< n₃ m p DG De
             (zeroRD-All< n₃ WG) (zeroRD-All< n₃ m)

 B-All< : RDAll< n₃ q B
 B-All< = sh-All< n₃ p q A₁ A₂ A₁-All< A₂-All<

 dS-All< : All< (WD WF W2) dS
 dS-All< =
  flatRD-All< WF W2 B₃
    (curryD-All< WG WF (WD m q) B₂
       (curryD-All< m n₂ q B B-All<))

\end{code}

The clause. Everything below the three binders is read off the three lemmas
named above.

\begin{code}

 S-clause : Dom ((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ) (μ-S {ρ} {σ} {τ}) dS
 S-clause F dF aF hF G dG aG hG a e ae ha =
  Dom-mono τ (μ-S F G a) (rect n₃ q B u₃) _ body fin
  where
   u₂ : Tup n₂
   u₂ = cmb WG WF dG dF

   u₃ : Tup n₃
   u₃ = cmb m n₂ e u₂

   Au₂ : All< n₂ u₂
   Au₂ = cmb-All< WG WF dG dF aG aF

   Au₃ : All< n₃ u₃
   Au₃ = cmb-All< m n₂ e u₂ ae Au₂

   e⊴ : e ⊴ u₃
   e⊴ = cmb-⊴-left m n₂ e u₂

   dG⊴ : dG ⊴ u₃
   dG⊴ = ⊴-trans WG n₂ n₃ dG u₂ u₃
           (cmb-⊴-left WG WF dG dF) (cmb-⊴-right m n₂ e u₂)

   dF⊴ : dF ⊴ u₃
   dF⊴ = ⊴-trans WF n₂ n₃ dF u₂ u₃
           (cmb-⊴-right WG WF dG dF) (cmb-⊴-right m n₂ e u₂)

   ea : Tup m
   ea = rect n₃ m De u₃

   fa : Tup WF
   fa = rect n₃ WF DF u₃

   ga : Tup WG
   ga = rect n₃ WG DG u₃

   Aea : All< m ea
   Aea = rect-All< n₃ m De u₃ (zeroRD-All< n₃ m) Au₃

   Afa : All< WF fa
   Afa = rect-All< n₃ WF DF u₃ (zeroRD-All< n₃ WF) Au₃

   Aga : All< WG ga
   Aga = rect-All< n₃ WG DG u₃ (zeroRD-All< n₃ WG) Au₃

   hea : Dom ρ a ea
   hea = Dom-mono ρ a e ea ha (rect-⊴ n₃ m u₃ e e⊴)

   hfa : Dom (ρ ⇒ σ ⇒ τ) F fa
   hfa = Dom-mono (ρ ⇒ σ ⇒ τ) F dF fa hF (rect-⊴ n₃ WF u₃ dF dF⊴)

   hga : Dom (ρ ⇒ σ) G ga
   hga = Dom-mono (ρ ⇒ σ) G dG ga hG (rect-⊴ n₃ WG u₃ dG dG⊴)

   h1 : Dom (σ ⇒ τ) (F a) (rect n₃ (WD p q) A₁ u₃)
   h1 = Dom-mono (σ ⇒ τ) (F a) _ _ (hfa a ea Aea hea)
          (rect-ssub n₃ m (WD p q) DF De u₃)

   h2 : Dom σ (G a) (rect n₃ p A₂ u₃)
   h2 = Dom-mono σ (G a) _ _ (hga a ea Aea hea)
          (rect-ssub n₃ m p DG De u₃)

   A2All : All< p (rect n₃ p A₂ u₃)
   A2All = rect-All< n₃ p A₂ u₃ A₂-All< Au₃

   body : Dom τ (F a (G a)) (rect n₃ q B u₃)
   body = Dom-mono τ (F a (G a)) _ _
            (h1 (G a) (rect n₃ p A₂ u₃) A2All h2)
            (rect-ssub n₃ p q A₁ A₂ u₃)

   d1 : Tup W2
   d1 = rect WF W2 (rdOf WF W2 dS) dF

   d2 : Tup (WD m q)
   d2 = rect WG (WD m q) (rdOf WG (WD m q) d1) dG

   g1 : rect WF W2 B₃ dF ⊑ d1
   g1 = rect-⊑RD WF W2 B₃ (rdOf WF W2 dS) (flatRD-⊒ WF W2 B₃) dF

   g2 : rect n₂ (WD m q) B₂ u₂ ⊑ d2
   g2 = ⊑-trans (WD m q) _ _ _
          (rect-curry WG WF (WD m q) B₂ dG dF)
          (rect-⊑RD WG (WD m q)
             (rdOf WG (WD m q) (rect WF W2 B₃ dF))
             (rdOf WG (WD m q) d1)
             (rdOf-mono WG (WD m q) (rect WF W2 B₃ dF) d1 g1)
             dG)

   fin : rect n₃ q B u₃ ⊑ rect m q (rdOf m q d2) e
   fin = ⊑-trans q _ _ _
           (rect-curry m n₂ q B e u₂)
           (rect-⊑RD m q (rdOf m q (rect n₂ (WD m q) B₂ u₂))
              (rdOf m q d2)
              (rdOf-mono m q (rect n₂ (WD m q) B₂ u₂) d2 g2)
              e)

\end{code}
