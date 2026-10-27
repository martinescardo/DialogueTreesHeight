The fundamental theorem, and the conjecture.

Every clause is proved: `Zero`, `Succ`, `Ω` and `K` in the module Predicate,
`S` in the module SClause, the recursor in the module IterClause, and
application is the clause for an arrow read forwards. An induction on terms
therefore gives every closed term of the oracle language a datum below `ε₀`
that dominates its majorant, and at ground type that is `μᵀ t < ε₀`, which is
the hypothesis of MajorantAll.dialogue-height-<-ε₀.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.DialogueTrees.Fundamental
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT
open import EffectfulForcing.MFPSAndVariations.MFPS-XXIX using (dialogue-tree)
open import DialogueTreesHeight.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; S-<-ε₀ ; Z<ε₀)
open import DialogueTreesHeight.BrouwerOrdinals.MoveTuple fe
 using (Tup ; All<)
open import DialogueTreesHeight.BrouwerOrdinals.Rect fe
 using (rect ; rdOf ; rect-All< ; rdOf-All<)
open import DialogueTreesHeight.BrouwerOrdinals.RectAlgebra fe
 using (zeroTup ; zeroTup-All<)
open import DialogueTreesHeight.DialogueTrees.Constructive fe
 using (height)
open import DialogueTreesHeight.DialogueTrees.MajorantAll fe
 using (μᵀ ; dialogue-height-<-ε₀)
open import DialogueTreesHeight.DialogueTrees.Predicate fe
 using (wd ; Dom ; Dom-<-ε₀ ; Zero-clause ; Succ-clause ; Ω-clause ;
        K-clause ; app-clause)
open import DialogueTreesHeight.DialogueTrees.SClause fe
 using (dS ; dS-All< ; S-clause)
open import DialogueTreesHeight.DialogueTrees.IterClause fe
 using (dI ; dI-All< ; Iter-clause)

\end{code}

The induction on terms.

\begin{code}

fundamental : {σ : type} (t : TΩ σ)
            → Σ d ꞉ Tup (wd σ) , (All< (wd σ) d × Dom σ (μᵀ t) d)
fundamental Ω =
 (S Z , (Z , ⋆)) , ((S-<-ε₀ Z Z<ε₀ , (Z<ε₀ , ⋆)) , Ω-clause Z)
fundamental Zero =
 zeroTup 1 , (zeroTup-All< 1 , Zero-clause (zeroTup 1))
fundamental Succ =
 zeroTup 2 , (zeroTup-All< 2 , Succ-clause (zeroTup 2))
fundamental (Iter {σ}) =
 dI σ , (dI-All< σ , Iter-clause σ)
fundamental (K {σ} {τ}) =
 zeroTup (wd (σ ⇒ τ ⇒ σ)) ,
 (zeroTup-All< (wd (σ ⇒ τ ⇒ σ)) , K-clause σ τ (zeroTup (wd (σ ⇒ τ ⇒ σ))))
fundamental (S {ρ} {σ} {τ}) =
 dS ρ σ τ , (dS-All< ρ σ τ , S-clause ρ σ τ)
fundamental (_·_ {σ} {τ} t u) =
 rect (wd σ) (wd τ) (rdOf (wd σ) (wd τ) d) e ,
 (rect-All< (wd σ) (wd τ) (rdOf (wd σ) (wd τ) d) e
    (rdOf-All< (wd σ) (wd τ) d ad) ae ,
  app-clause σ τ (μᵀ t) (μᵀ u) d e hd ae he)
 where
  ih₁ : Σ d ꞉ Tup (wd (σ ⇒ τ)) , (All< (wd (σ ⇒ τ)) d × Dom (σ ⇒ τ) (μᵀ t) d)
  ih₁ = fundamental t

  ih₂ : Σ e ꞉ Tup (wd σ) , (All< (wd σ) e × Dom σ (μᵀ u) e)
  ih₂ = fundamental u

  d : Tup (wd (σ ⇒ τ))
  d = pr₁ ih₁

  ad : All< (wd (σ ⇒ τ)) d
  ad = pr₁ (pr₂ ih₁)

  hd : Dom (σ ⇒ τ) (μᵀ t) d
  hd = pr₂ (pr₂ ih₁)

  e : Tup (wd σ)
  e = pr₁ ih₂

  ae : All< (wd σ) e
  ae = pr₁ (pr₂ ih₂)

  he : Dom σ (μᵀ u) e
  he = pr₂ (pr₂ ih₂)

\end{code}

At ground type the datum is a single code, so the majorant is below `ε₀`.

\begin{code}

μᵀ-<-ε₀ : (t : TΩ ι) → μᵀ t < ε₀
μᵀ-<-ε₀ t = Dom-<-ε₀ (μᵀ t) (pr₁ (fundamental t))
              (pr₂ (pr₂ (fundamental t)))
              (pr₁ (pr₂ (fundamental t)))

\end{code}

The conjecture.

\begin{code}

dialogue-tree-height-<-ε₀ : (t : T ((ι ⇒ ι) ⇒ ι))
                          → height (dialogue-tree t) < ε₀
dialogue-tree-height-<-ε₀ t =
 dialogue-height-<-ε₀ t (μᵀ-<-ε₀ (embedding t · Ω))

\end{code}
