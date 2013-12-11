open import Data.Maybe.NP
open import Data.Product
open import Data.Nat
open import Data.One
open import Data.Zero
import Nested.PTS as PTS
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)
open import Scope
open import Function

module Nested.PTS.F where

data Sort : Set where
  ★ ∎ : Sort

data _∶κ_ : (s₁ s₂ : Sort) → Set where
  ★∶∎ : ★ ∶κ ∎

data ⟨_,_,_⟩∈R : (s₁ s₂ s₃ : Sort) → Set where
  `→` : ⟨ ★ , ★ , ★ ⟩∈R
  `∀` : ⟨ ∎ , ★ , ★ ⟩∈R

open PTS Sort
open Typing _∶κ_ ⟨_,_,_⟩∈R

∀' : ∀ {α} → Scope 𝟙 Ty α → Ty α
∀' τ = Π (` ★) τ

∀'' : ∀ {α} → ∀Scope𝟙 Ty α → Ty α
∀'' τ = ∀' (abs™ τ)

syntax ∀'' (λ x → τ) = ∀⟨ x ⟩ τ

Λ : ∀ {α} → Scope 𝟙 Tm α → Tm α
Λ t = ƛ (` ★) t

Λ' : ∀ {α} → ∀Scope𝟙 Tm α → Tm α
Λ' t = Λ (abs™ t)

syntax Λ' (λ x → t) = Λ⟨ x ⟩ t

ƛ' : ∀ {A} → Ty A → ∀Scope𝟙 Tm A → Tm A
ƛ' σ f = ƛ σ (abs™ f)

syntax ƛ' τ (λ x → t) = ƛ⟨ x ∶ τ ⟩ t

Π' : ∀ {A} → Ty A → ∀Scope𝟙 Ty A → Ty A
Π' σ f = Π σ (abs™ f)

syntax Π' τ (λ x → t) = Π⟨ x ∶ τ ⟩ t

infixr 0 _⇒_
_⇒_ : ∀ {α} → Ty α → Ty α → Ty α
σ ⇒ τ = Π⟨ _ ∶ σ ⟩ map™ old τ

{-
_⊢⇒_ : ∀ {α} {Γ} {σ τ : Ty α} → Γ ⊢ σ ∶ ` ★ → Γ ⊢ τ ∶ ` ★ → Γ ⊢ σ ⇒ τ ∶ ` ★
⊢σ ⊢⇒ ⊢τ = Π `→` ⊢σ {!map⊢ ? ⊢τ!}
-}

{-
there' : ∀ {b ω α} {b# : b # α} {x τ σ} {Γ : Cx ω α}
           (x∶τ∈Γ : ⟨ x ∶ τ ⟩∈ Γ                                              )
         →         ----------------------------------------------------------
                   ⟨ coerceᴺ (⊆-# b#) x ∶ impTmWith b# τ ⟩∈ (Γ ,, b# ∶ σ)
there' x = there (exportᴺ?∘coerceᴺ-success _) ≡.refl x

V′ : ∀ b {α} → Tm (b ◅ α)
V′ b = V (nameᴮ b)

V` : ∀ k x {α} → Tm ((k + x) ◅… α)
V` k x = V (name◅… k x)
-}
V₀ : ∀ {A B} → B → Tm (A ▹ B)
V₀ x = V (new x)
V₁ : ∀ {A B C} → B → Tm (A ▹ B ▹ C)
V₁ x = V (old (new x))
V₂ : ∀ {A B C D} → B → Tm (A ▹ B ▹ C ▹ D)
V₂ x = V (old (old (new x)))
{-
V₃ = V` 3
V₄ = V` 4
V₅ = V` 5
V₆ = V` 6
V₇ = V` 7
V₈ = V` 8
-}

module IdentityExample where
  idT : Tm 𝟘
  idT = Λ⟨ A ⟩ ƛ⟨ x ∶ V₀ A ⟩ V₀ x

  idτ : Ty 𝟘
  idτ = ∀⟨ A ⟩ V₀ A ⇒ V₀ A

  idτ∶★′ : ε ,, ` ★ ⊢ (V₀ _) ⇒ (V₀ _) ∶ ` ★
  idτ∶★′ = Π `→` (V here) (V (there here))

  idτ∶★ : ε ⊢ idτ ∶ ` ★
  idτ∶★ = Π `∀` (` ★∶∎) idτ∶★′

  idT∶idτ : ε ⊢ idT ∶ idτ
  idT∶idτ = ƛ idτ∶★ (ƛ idτ∶★′ (V here))

module AppExample where
  -- « Λ A B → λ (f : A → B) (x : A) → f x »
  apT : Tm 𝟘
  apT = Λ⟨ A ⟩ Λ⟨ B ⟩ ƛ⟨ f ∶ V₁ A ⇒ V₀ B ⟩ ƛ⟨ x ∶ V₂ A ⟩ (V₁ f · V₀ x)

  -- « ∀ A B → (A → B) → A → B »
  apτ : Tm 𝟘
  apτ = ∀⟨ A ⟩ (∀⟨ B ⟩ ((V₁ A ⇒ V₀ B) ⇒ V₁ A ⇒ V₀ B))

  apτ∶★ : ε ⊢ apτ ∶ ` ★
  apτ∶★ = Π `∀` (` ★∶∎)
               (Π `∀` (` ★∶∎)
               (Π `→` (Π `→` (V here) (V (there here)))
               (Π `→` (V (there here)) (V (there (there here))))))
-- -}
-- -}
-- -}
-- -}
