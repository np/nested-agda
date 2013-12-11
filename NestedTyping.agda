module NestedTyping where

open import Type
open import Data.One
open import Function.NP
open import Scope

---- ty : type.
data Ty : ★ where
  ---- arr : ty -> ty -> ty.
  _⇒_ : (σ τ : Ty) → Ty
  ---- nat : ty.
  nat  : Ty

---- tm : type.
data Tm (A : ★) : ★ where
  V    : A → Tm A
  ---- app : tm -> tm -> tm
  _·_  : Tm A → Tm A → Tm A
  ---- lam : (tm -> tm) -> tm
  ƛ    : Scope 𝟙 Tm A → Tm A
infixl 4 _·_

_→™_ : ★ → ★ → ★
A →™ B = Tm A → Tm B

-- Substitutions
_⇶_ : ★ → ★ → ★
A ⇶ B = A → Tm B

map™ : ∀ {A B} → (A → B) → A →™ B
map™ f (V x)   = V (f x)
map™ f (t · u) = map™ f t · map™ f u
map™ f (ƛ t)   = ƛ (map™ (map▹ f) t)

⇑™ : ∀ {A B} → A ⇶ B → (A ▹ 𝟙) ⇶ (B ▹ 𝟙)
(⇑™ θ) (new x) = V (new x)
(⇑™ θ) (old x) = map™ old (θ x)

infixr 1 _=<<™_
_=<<™_ : ∀ {A B} → A ⇶ B → A →™ B
θ =<<™ V x   = θ x
θ =<<™ t · u = (θ =<<™ t) · (θ =<<™ u)
θ =<<™ ƛ t   = ƛ (⇑™ θ =<<™ t)

join™ : ∀ {A} → Tm (Tm A) → Tm A
join™ = _=<<™_ id

_>>=™_ : ∀ {A B} → Tm A → (A → Tm B) → Tm B
t >>=™ f = f =<<™ t

[0≔_] : ∀ {A} → Tm A → A ▹ 𝟙 → Tm A
[0≔ u ] (new x) = u
[0≔ u ] (old x) = V x

_∙_ : ∀ {A} → Tm (A ▹ 𝟙) → Tm A → Tm A
t ∙ u = t >>=™ [0≔ u ]

--i★ : ★ → ★₁
--i★ A = A → Ty → ★

{-
i★₁ : Set₂
i★₁ = Ty → ★₁

_⇴_ : ∀ {A} → i★ A → i★ A → ★
F ⇴ G = ∀ {i j} → F i j → G i j

_⇴₁_ : i★ → i★₁ → ★₁
F ⇴₁ G = ∀ {i} → F i → G i
-}

{-
data _,_ {A} (Γ : i★ A) τ : i★ (A ▹ 𝟙) where
  here  : new _ ∶ τ ∈ (Γ , τ)
  there  : ∀ {x σ} → x ∶ σ ∈ Γ → old x ∶ σ ∈ (Γ , τ)
-}

open IndexedScope2 {Ty}

  {-
elim, : ∀ {τ Γ Δ} → Δ τ → (Γ ⇴ Δ) → (Γ , τ) ⇴ Δ
elim, h _ here      = h
elim, _ t (there x) = t x
-}

---- of : tm -> ty -> type.
data _⊢_∶_ {A} (Γ : i★ A) : i★ (Tm A) where
  V   : ∀ {x τ}
          (⊢x : x ∶ τ ∈ Γ)
        → ----------------
            Γ ⊢ V x ∶ τ

  ---- of/app : {t : tm}{u : tm}{sg : ty}{tau : ty} of t (arr sg tau) -> of u sg -> of (app t u) tau.
  _·_ : ∀ {t u σ τ}
          (⊢t : Γ ⊢ t ∶ (σ ⇒ τ))
          (⊢u : Γ ⊢ u ∶ σ)
        → -----------------------
            Γ ⊢ (t · u) ∶ τ

  ---- of/lam : {t : tm -> tm}{sg : ty}{tau : ty}
  ----          ({x : tm} {of/x : of x sg} of (t x) tau) -> of (lam t) (arr sg tau).
  ƛ   : ∀ {t σ τ}
          (⊢t : (Γ , σ) ⊢ t ∶ τ)
        → -----------------------
           Γ ⊢ ƛ t ∶ (σ ⇒ τ)

⊢ƛ : ∀ {A} {f : ∀Scope𝟙 Tm A} {Γ} {σ τ} → (∀ {B} {x : B} {Δ : i★ B} → x ∶ σ ∈ Δ → (Γ , σ ⇒ Δ) ⊢ f x ∶ τ) → (Γ , σ) ⊢ f 0₁ ∶ τ
⊢ƛ ⊢f = ⊢f 0₁

Of : ∀ {A} → i★ A → i★ (Tm A)
Of = _⊢_∶_

                 {-
_⇴™_ : ∀ {A} → i★ A → i★ A → ★
Γ ⇴™ Δ = Of Γ ⇴ Of Δ

-- Substitutions
_⊢⇶_ : ∀ {A} → i★ (Tm A) → i★ A → ★
Γ ⊢⇶ Δ = Γ ⇴ Of Δ
-}

map, : ∀ {A B} {Γ : i★ A} {f : A → B} {Δ τ} → (∀ {x σ} → Γ x σ → Δ (f x) σ) → ∀ {x σ} → (Γ , τ) x σ → (Δ , τ) (map▹ f x) σ
map, f (here x)  = here x
map, f (there x) = there (f x)

module Map⊢ where
  [_] : ∀ {A B} {f : A → B} {Γ : i★ A} {Δ : i★ B} → (∀ {x σ} → Γ x σ → Δ (f x) σ) → ∀ {t σ} → Γ ⊢ t ∶ σ → Δ ⊢ (map™ f t) ∶ σ
  [ f ](V x)   = V (f x)
  [ f ](t · u) = [ f ] t · [ f ] u
  [ f ](ƛ t)   = ƛ ([ map, f ] t)

module Subst⊢ where
  ⊢⇑_ : ∀ {A B} {Γ : i★ A} {Δ : i★ B} {f : A → Tm B} {τ}
       → (∀ {x σ} → Γ x σ → Δ ⊢ f x ∶ σ)
       → ∀ {x σ} → (Γ , τ) x σ → (Δ , τ) ⊢ (⇑™ f x) ∶ σ
  (⊢⇑ θ) (here x)  = V (here x)
  (⊢⇑ θ) (there x) = Map⊢.[ there ](θ x)

  [_] : ∀ {A B Γ} {Δ : i★ B} {f : A → Tm B} → (∀ {i j} → Γ i j → Δ ⊢ V i >>=™ f ∶ j) → ∀ {t : Tm A}{τ} → Γ ⊢ t ∶ τ → Δ ⊢ t >>=™ f ∶ τ -- Γ ⇴™ Δ
  [ θ ](V x)   = θ x
  [ θ ](t · u) = [ θ ] t · [ θ ] u
  [ θ ](ƛ t)   = ƛ ([ ⊢⇑ θ ] t)

⊢[0≔_] : ∀ {A Γ} {u : Tm A} {σ x γ}
         → Γ ⊢ u ∶ σ
         → x ∶ γ ∈ (Γ , σ)
         → Γ ⊢ V x >>=™ [0≔ u ] ∶ γ
⊢[0≔ ⊢u ] (here  ⊢x) = ⊢u
⊢[0≔ ⊢u ] (there ⊢x) = V ⊢x

_⊢∙_ : ∀ {A Γ σ τ t}{u : Tm A}
       → (Γ , σ) ⊢ t ∶ τ
       → Γ ⊢ u ∶ σ
       → Γ ⊢ (t ∙ u) ∶ τ
⊢t ⊢∙ ⊢u = Subst⊢.[ ⊢[0≔ ⊢u ] ] ⊢t

infix 2 _↝_
---- red : tm -> tm -> type.
data _↝_ {A} : Tm A → Tm A → ★ where

  ---- red/beta : {t : tm -> tm}{u : tm} red (app (lam t) u) (t u).
  β : ∀ t u →
      ƛ t · u ↝ t ∙ u

  ---- red/app1 : {t : tm}{t' : tm}{u : tm}
  ----            red t t' -> red (app t u) (app t' u).
  _·₁_ : ∀ {t t′} → t ↝ t′ → ∀ u → t · u ↝ t′ · u

---- preserve : {t : tm}{t':tm}{tau : ty} red t t' -> of t tau -> of t' tau -> type.
data Preserve {A Γ} : ∀ {t : Tm A} {t′ τ} →
                    t ↝ t′ →
                    Γ ⊢ t  ∶ τ →
                    Γ ⊢ t′ ∶ τ → ★ where
  ---- preserve/beta : {t : tm -> tm}{u : tm}{sg : ty}{tau : ty}
  ----                 {of/t : {x:tm}{of/x:of x sg} of (t x) tau}
  ----                 {of/u : of u sg}
  ----                 preserve (app (lam t) u) (t u) tau
  ----                          (red/beta t u)
  ----                          (of/app (lam t) u sg tau (of/lam t sg tau of/t) of/u) 
  ----                          (of/t u of/u).
  β : ∀ t (u : Tm A) {σ τ}
        (⊢t : (Γ , σ) ⊢ t ∶ τ)
        (⊢u : Γ ⊢ u ∶ σ) →
        Preserve (β t u) (ƛ ⊢t · ⊢u) (⊢t ⊢∙ ⊢u)

  ---- preserve/app1 : {t:tm}{t':tm}{red/tt':red t t'}{sg:ty}{tau:ty}
  ----                 {of/t:of t (arr sg tau)}
  ----                 {of/t':of t' (arr sg tau)}
  ----                 {u:tm}{of/u:of u sg}
  ----                 preserve t t' (arr sg tau) red/tt' of/t of/t' ->
  ----                 preserve (app t u) (app t' u) tau
  ----                   (red/app1 t t' u red/tt')
  ----                   (of/app t  u sg tau of/t  of/u)
  ----                   (of/app t' u sg tau of/t' of/u).
  _·₁_ : ∀ {t t′} {t↝t′ : t ↝ t′} {σ τ}
           {⊢t  : Γ ⊢ t  ∶ (σ ⇒ τ)}
           {⊢t′ : Γ ⊢ t′ ∶ (σ ⇒ τ)} →
         ∀ u → {⊢u : Γ ⊢ u ∶ σ} →
           Preserve t↝t′ ⊢t ⊢t′ →
           Preserve (t↝t′ ·₁ u) (⊢t · ⊢u) (⊢t′ · ⊢u)

preserve : ∀ {A Γ} {t : Tm A} {t′ τ} →
                    t ↝ t′ →
                    Γ ⊢ t  ∶ τ →
                    Γ ⊢ t′ ∶ τ
preserve (β t u)     (ƛ ⊢t · ⊢u) = ⊢t ⊢∙ ⊢u
preserve (t↝t′ ·₁ u) (⊢t · ⊢u)   = let ⊢t′ = preserve t↝t′ ⊢t in ⊢t′ · ⊢u
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
