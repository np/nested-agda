module Scope where

open import Type
open import Data.One
open import Function.NP
open import Relation.Binary.PropositionalEquality as ≡

infixl 5 _▹_
data _▹_ (A : ★) (B : ★) : ★ where
  old : A → A ▹ B
  new : B → A ▹ B

map▹ : ∀ {A B C} → (A → B) → (A ▹ C) → (B ▹ C)
map▹ f (new x) = new x
map▹ f (old x) = old (f x)

map▹-id : ∀ {A C} {f : A → A} → f ≗ id → map▹ {C = C} f ≗ id
map▹-id f≗id (old x)   = cong old (f≗id x)
map▹-id f≗id (new x) = refl

map▹-∘ : ∀ {A B C D} {f : B → C} {g : A → B} {h : A → C} → h ≗ f ∘ g → map▹ {C = D} h ≗ map▹ f ∘ map▹ g
map▹-∘ h≗ (old x)   = cong old (h≗ x)
map▹-∘ h≗ (new x) = refl

map▹-ext : ∀ {A B C} {f g : A → B} → f ≗ g → map▹ {C = C} f ≗ map▹ g
map▹-ext f≗ (old x)   = cong old (f≗ x)
map▹-ext f≗ (new x) = refl

Succ : ★ → ★
Succ A = A ▹ 𝟙

Scope : ★ → (★ → ★) → ★ → ★
Scope B F A = F (A ▹ B)

GScope : ★ → (★ → ★) → ★ → ★
GScope B F A = Scope B F (F A)

∀Scope𝟙 : (★ → ★) → ★ → ★₁
∀Scope𝟙 F A = ∀ {B} → B → Scope B F A

∀Scope : ★ → (★ → ★) → ★ → ★₁
∀Scope B F A = ∀ {C} → (B → C) → Scope C F A

abs : ∀ {F A} → ∀Scope𝟙 F A → Scope 𝟙 F A
abs f = f _

abs' : ∀ {F A B} → ∀Scope B F A → Scope B F A
abs' f = f id

--absG₁ : ∀ {F A} → ∀Scope𝟙 F A → GScope 𝟙 F A
--absG₁ f = {!f!}

module IndexedScope1 {Ix : ★} where
    i★ : ★₁
    i★ = Ix → ★

    i★₁ : ★₂
    i★₁ = Ix → ★₁

    _⇴_ : i★ → i★ → ★
    F ⇴ G = ∀ {i} → F i → G i

    _⇴₁_ : i★ → i★₁ → ★₁
    F ⇴₁ G = ∀ {i} → F i → G i

    _∈_ : Ix → i★ → ★
    τ ∈ Γ = Γ τ

    data _,_ (Γ : i★) τ : i★ where
      here  : τ ∈ (Γ , τ)
      there : ∀ {σ} → σ ∈ Γ → σ ∈ (Γ , τ)

    elim, : ∀ {τ Γ Δ} → Δ τ → (Γ ⇴ Δ) → (Γ , τ) ⇴ Δ
    elim, h _ here      = h
    elim, _ t (there x) = t x

    map, : ∀ {Γ Δ τ} → (Γ ⇴ Δ) → ((Γ , τ) ⇴ (Δ , τ))
    map, f here      = here
    map, f (there x) = there (f x)

module IndexedScope2 {Ix : ★} where
    i★ : ★ → ★₁
    i★ A = A → Ix → ★

    _∶_∈_ : ∀ {A} → A → Ix → i★ A → ★
    x ∶ τ ∈ Γ = Γ x τ

    data _,_⇒_ {A} {B} (Γ : i★ A) τ (Δ : i★ B) : i★ (A ▹ B) where
      here   : ∀ {x}   → x ∶ τ ∈ Δ → new x ∶ τ ∈ (Γ , τ ⇒ Δ)
      there  : ∀ {x σ} → x ∶ σ ∈ Γ → old x ∶ σ ∈ (Γ , τ ⇒ Δ)

    -- i★𝟙 : i★ 𝟙
    -- i★𝟙 _ _ = 𝟙
    record i★𝟙 (_ : 𝟙) (_ : Ix) : ★ where
      constructor 0₁

    _,_ : ∀ {A} (Γ : i★ A) τ → i★ (A ▹ 𝟙)
    Γ , τ = Γ , τ ⇒ i★𝟙
