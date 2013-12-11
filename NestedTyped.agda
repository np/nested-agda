module NestedTyped where

open import Type
open import Function.NP using (id; _∘_; id-app)
open import Data.Product hiding (map) renaming (_,_ to _,,_)
open import Category.Applicative
            renaming (RawApplicative to Applicative; module RawApplicative to Applicative)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; _≗_)

data Ty : ★ where
  _⇒_ : (σ τ : Ty) → Ty
  nat  : Ty

i★ : ★₁
i★ = Ty → ★

i★₁ : ★₂
i★₁ = Ty → ★₁

_⇴_ : i★ → i★ → ★
F ⇴ G = ∀ {i} → F i → G i

_⇴₁_ : i★ → i★₁ → ★₁
F ⇴₁ G = ∀ {i} → F i → G i

_∈_ : Ty → i★ → ★
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

data _⊢_ (Γ : i★) : i★ where
  V   : ∀ {τ}
          (x : τ ∈ Γ)
        →  -----------
              Γ ⊢ τ

  _·_ : ∀ {σ τ}
          (t : Γ ⊢ (σ ⇒ τ))
          (u : Γ ⊢ σ)
        →  ------------------
               Γ ⊢ τ

  ƛ   : ∀ {σ τ}
          (t : (Γ , σ) ⊢ τ)
        → -------------------
               Γ ⊢ (σ ⇒ τ)

Tm : i★ → i★
Tm = _⊢_

_⇴™_ : i★ → i★ → ★
Γ ⇴™ Δ = Tm Γ ⇴ Tm Δ

-- Substitutions
_⇶_ : i★ → i★ → ★
Γ ⇶ Δ = Γ ⇴ Tm Δ

module Applicative™ {E : ★ → ★} (E-app : Applicative E) where
  open Applicative E-app public

  _⇴™E_ : i★ → i★ → ★
  Γ ⇴™E Δ = Tm Γ ⇴ (E ∘ Tm Δ)

  _⇶E_ : i★ → i★ → ★
  Γ ⇶E Δ = Γ ⇴ (E ∘ Tm Δ)

return : ∀ {Γ} → Γ ⇶ Γ
return = V

data ε : i★ where

map : ∀ {Γ Δ} → Γ ⇴ Δ → Γ ⇴™ Δ
map f (V x)   = V (f x)
map f (t · u) = map f t · map f u
map f (ƛ t)   = ƛ (map (map, f) t)

_∷_ : ∀ {Γ Δ τ} → Δ ⊢ τ → Γ ⇶ Δ → (Γ , τ) ⇶ Δ
_∷_ = elim,

wk : ∀ {Γ σ} → Γ ⇴™ (Γ , σ)
wk = map there

⇑_ : ∀ {τ Γ Δ} → Γ ⇶ Δ → (Γ , τ) ⇶ (Δ , τ)
⇑ θ = V here ∷ (wk ∘ θ)

[0≔_] : ∀ {Γ τ} → Γ ⊢ τ → (Γ , τ) ⇶ Γ
[0≔ t ] = t ∷ V

infixl 4 _=<<_
_=<<_ : ∀ {Γ Δ} → Γ ⇶ Δ → Γ ⇴™ Δ
θ =<< V x   = θ x
θ =<< t · u = (θ =<< t) · (θ =<< u)
θ =<< ƛ t   = ƛ (⇑ θ =<< t)

_>>=_ : ∀ {Γ Δ σ} → Γ ⊢ σ → Γ ⇶ Δ → Δ ⊢ σ
t >>= θ = θ =<< t

_>=>_ : ∀ {Γ Δ ψ} → Γ ⇶ Δ → Δ ⇶ ψ → Γ ⇶ ψ
(θ >=> φ) x = θ x >>= φ

_<=<_ : ∀ {Γ Δ ψ} → Δ ⇶ ψ → Γ ⇶ Δ → Γ ⇶ ψ
(φ <=< θ) x = θ x >>= φ

  -->>=-assoc : ∀ {Γ Δ ψ τ} (t : Γ ⊢ τ) (u : Γ ⇶ Δ) (f : Δ ⇶ ψ) → t >>= (λ x → u x >>= f) ≡ (t >>= u) >>= f
  -->>=-assoc t u f = {!!}

join⊢ : ∀ {Γ} → Tm (Tm Γ) ⇴ Tm Γ
join⊢ = _=<<_ id

{-
-- generalized by Traverse
module PureTraverse (Env : i★ → i★ → ★)
                    (_∙_ : ∀ {Γ Δ} → Env Γ Δ → Γ ⇶ Δ)
                    (⇑ : ∀ {Γ Δ σ} → Env Γ Δ → Env (Γ , σ) (Δ , σ)) where
  [_] : ∀ {Γ Δ} → Env Γ Δ → Γ ⇴™ Δ
  [ θ ](V x)   = θ ∙ x
  [ θ ](t · u) = [ θ ] t · [ θ ] u
  [ θ ](ƛ t)   = ƛ ([ ⇑ θ ] t)

-- generalized by DerivedFromTraverse
module DerivedFromPureTraverse where
  module MapKit where
    MapEnv : i★ → i★ → ★
    MapEnv = _⇴_

    ⇑_ : ∀ {Γ Δ σ} → Γ ⇴ Δ → (Γ , σ) ⇴ (Δ , σ)
    ⇑_ = map,

  map⊢ : ∀ {Γ Δ} → Γ ⇴ Δ → Γ ⇴™ Δ
  map⊢ = PureTraverse.[ MapEnv ] (λ f x → V (f x)) ⇑_ where open MapKit

  module SubstKit where
    ⇑_ : ∀ {Γ Δ σ} → Γ ⇶ Δ → (Γ , σ) ⇶ (Δ , σ)
    (⇑ f) here      = V here
    (⇑ f) (there x) = map⊢ there (f x)

  subst⊢ : ∀ {Γ Δ} → Γ ⇶ Δ → Γ ⇴™ Δ
  subst⊢ θ = [ θ ]
    where open SubstKit
          open PureTraverse _⇶_ (λ x → x) ⇑_

  join⊢ : ∀ {Γ} → Tm (Tm Γ) ⇴ Tm Γ
  join⊢ = subst⊢ id

-- generalized by Traverse
module TraverseSubstKitByHand {E : ★ → ★} (E-app : Applicative E) where
  open Applicative™ E-app
  open ⊢Ops-ByHand

  ⇑_ : ∀ {Γ Δ σ} → Γ ⇶E Δ → (Γ , σ) ⇶E (Δ , σ)
  (⇑ f) here      = pure (V here)
  (⇑ f) (there x) = Map⊢.[ there ] <$> f x

  [_] : ∀ {Γ Δ} → Γ ⇶E Δ → Γ ⇴™E Δ
  [ f ](V x)   = f x
  [ f ](t · u) = pure _·_ ⊛ [ f ] t ⊛ [ f ] u
  [ f ](ƛ t)   = pure ƛ ⊛ [ ⇑ f ] t

module Traverse {E : ★ → ★}
                (E-app : Applicative E)
                (Env : i★ → i★ → ★)
                (_∙_ : ∀ {Γ Δ} → Env Γ Δ → Γ ⇴ (E ∘ Tm Δ))
                (⇑_ : ∀ {Γ Δ σ} → Env Γ Δ → Env (Γ , σ) (Δ , σ)) where
  open Applicative™ E-app

  [_] : ∀ {Γ Δ} → Env Γ Δ → Γ ⇴™E Δ
  [ θ ](V x)   = θ ∙ x
  [ θ ](t · u) = pure _·_ ⊛ [ θ ] t ⊛ [ θ ] u
  [ θ ](ƛ t)   = pure ƛ ⊛ [ ⇑ θ ] t

module DerivedFromTraverse where
  map⊢ : ∀ {Γ Δ} → Γ ⇴ Δ → Γ ⇴™ Δ
  map⊢ t = [ t ]
    where open Traverse id-app _⇴_ (λ f x → V (f x)) map,

  subst⊢ : ∀ {Γ Δ} → Γ ⇶ Δ → Γ ⇴™ Δ
  subst⊢ θ = [ θ ]
     where
        ⇑_ : ∀ {Γ Δ σ} → Γ ⇶ Δ → (Γ , σ) ⇶ (Δ , σ)
        (⇑ f) here      = V here
        (⇑ f) (there x) = map⊢ there (f x)
        open Traverse id-app _⇶_ (λ x → x) ⇑_

  join⊢ : ∀ {Γ} → Tm (Tm Γ) ⇴ Tm Γ
  join⊢ = subst⊢ id

open DerivedFromTraverse
-}

infixl 4 _∙_
_∙_ : ∀ {τ σ Γ} → (Γ , σ) ⊢ τ → Γ ⊢ σ → Γ ⊢ τ
t ∙ u = t >>= [0≔ u ]

β-red : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ τ
β-red (ƛ t · u) = t ∙ u
β-red t = t

infix 2 _↝_
data _↝_ {Γ τ} : Γ ⊢ τ → Γ ⊢ τ → ★ where
  β     : ∀ {σ} {t : (Γ , σ) ⊢ τ} {u} → (ƛ t · u) ↝ t ∙ u
  _·₁_  : ∀ {σ} {M M'} → M ↝ M' → (N : Γ ⊢ σ) → M · N ↝ M' · N
  refl  : ∀ {M} → M ↝ M
  trans : ∀ {M N M'} → M ↝ N → N ↝ M' → M ↝ M'

data Val {Γ} : ∀ {τ} → Γ ⊢ τ → ★ where
  ƛ : ∀ {σ τ} {t : (Γ , σ) ⊢ τ} → Val (ƛ t)
  --cst : Val {!!}

data Halts {Γ τ} (M : Γ ⊢ τ) : ★ where
  halts : ∀ {V} → M ↝ V → Val V → Halts M

Reduce : ∀ {Γ} τ → Γ ⊢ τ → ★
Reduce nat         M = Halts M
Reduce {Γ} (σ ⇒ τ) M = Halts M × ({N : Γ ⊢ σ} → Reduce σ N → Reduce τ (M · N))

{-
-- Agda should accept it!
data Reduce {Γ} : ∀ τ → Γ ⊢ τ → ★ where
  nat : ∀ {M} → Halts M → Reduce nat M
  _⇒_ : ∀ {σ τ M} → Halts M → (Reduce σ → Reduce τ) → Reduce (σ ⇒ τ)
-}

halts-closed : ∀ {Γ τ} {M M' : Γ ⊢ τ} → M ↝ M' → Halts M' → Halts M
halts-closed ms (halts r' v) = halts (trans ms r') v

closed : ∀ {Γ} τ {M M' : Γ ⊢ τ} → M ↝ M' → Reduce τ M' → Reduce τ M
closed nat     ms rM' = halts-closed ms rM'
closed (σ ⇒ τ) ms (h ,, rM') = halts-closed ms h ,, (λ {N} rN → closed _ (ms ·₁ N) (rM' rN))

{-
RedSub : ∀ {Γ Δ} → Γ ⇶ Δ → ★
RedSub {Γ} {Δ} θ = ∀ {τ} (x : Γ τ) → Reduce _ (θ x)

cons : ∀ {Γ Δ τ M} {θ : Γ ⇶ Δ} → Reduce {Δ} τ M → RedSub θ → RedSub (M ∷ θ)
cons rM rθ here      = rM
cons rM rθ (there x) = rθ x
-}

RedSub : ∀ {Γ} → Γ ⇶ ε → ★
RedSub {Γ} θ = ∀ {τ} (x : Γ τ) → Reduce _ (θ x)

cons : ∀ {Γ τ M} {θ : Γ ⇶ ε} → Reduce {ε} τ M → RedSub θ → RedSub (M ∷ θ)
cons rM rθ here      = rM
cons rM rθ (there x) = rθ x

--lookup : ∀ {Γ Δ} → Γ ⇶ Δ → Γ ⇴ Δ
--lookup = {!!}

-- _⇴R_ : i★ → i★ → ★
-- F ⇴R G = ∀ {i} → Reduce _ (F i) → Reduce _ (G i)

-->>=

infix 2 _≈_
_≈_ : ∀ {Γ Δ} (θ φ : Γ ⇶ Δ) → ★
_≈_ {Γ} θ φ = ∀ {τ} (x : Γ τ) → θ x ≡ φ x

liftM : ∀ {Γ Δ} → Γ ⇴ Δ → Γ ⇴™ Δ
liftM f t = t >>= (V ∘ f)

map>>=' : (λ {x} {y} → map {x} {y}) ≡ liftM
map>>=' = {!!}

map>>= : ∀ {Γ Δ τ} {f : Γ ⇴ Δ} {t : Γ ⊢ τ} → map f t ≡ t >>= (V ∘ f)
map>>= = {!!}

⇑'_ : ∀ {τ Γ Δ} → Γ ⇶ Δ → (Γ , τ) ⇶ (Δ , τ)
⇑' θ = V here ∷ (liftM there ∘ θ)

⇑'-hom : ∀ {Γ Δ ψ τ} (θ : Γ ⇶ Δ) (φ : Δ ⇶ ψ) → ⇑'_ {τ} (θ >=> φ) ≈ ⇑' θ >=> ⇑' φ
⇑'-hom θ φ here = ≡.refl
⇑'-hom θ φ (there x) = {!((⇑' θ) >=> (⇑' φ)) (there x)!}

⇑-hom : ∀ {Γ Δ ψ τ} (θ : Γ ⇶ Δ) (φ : Δ ⇶ ψ) → ⇑_ {τ} (θ >=> φ) ≈ ⇑ θ >=> ⇑ φ
⇑-hom θ φ here = ≡.refl
⇑-hom θ φ (there x) = {!rewrite map>>=' = {!!}!}


-- apply (θ ∘ φ) = apply θ ∘ apply φ
bar : ∀ {Γ Δ ψ τ} (θ : Γ ⇶ Δ) (φ : Δ ⇶ ψ) (M : Γ ⊢ τ) → M >>= (θ >=> φ) ≡ (M >>= θ) >>= φ
bar θ φ (V x) = ≡.refl
bar θ φ (M · M₁) = ≡.cong₂ _·_ (bar θ φ M) (bar _ _ M₁)
bar θ φ (ƛ M) = ≡.cong ƛ {!bar ? ? M!}

-- (⇑ θ >=> [0≔ N ]) = N ∷ θ
-- (⇑ θ >=> (N ∷ V)) = N ∷ θ

boo : ∀ {Γ Δ σ} (N : Δ ⊢ σ) (θ : Γ ⇶ Δ) → _≡_ {A = (Γ , σ) ⇶ Δ} (N ∷ θ) ((V here ∷ (wk ∘ θ)) >=> (N ∷ V))
boo = {!!}

foo : ∀ {Γ Δ τ σ} {N : Δ ⊢ σ} {θ : Γ ⇶ Δ} (M : (Γ , σ) ⊢ τ) → M >>= (N ∷ θ) ≡ (M >>= ⇑ θ) >>= [0≔ N ]
foo {N = N} {θ} M rewrite boo N θ = bar (⇑ θ) [0≔ N ] M

-- main : ∀ {Γ Δ τ} {θ : Γ ⇶ Δ} (M : Γ ⊢ τ) → RedSub θ → Reduce τ (subst⊢ θ M)
main : ∀ {Γ τ} {θ : Γ ⇶ ε} (M : Γ ⊢ τ) → RedSub θ → Reduce τ (M >>= θ)
main (V x)    rθ = rθ x
main (M₁ · M₂)  rθ with main M₁ rθ
... | h ,, f = f (main M₂ rθ)
main {τ} (ƛ M) rθ = halts refl ƛ ,, λ {N} rN → closed _ β (≡.subst (Reduce _) (foo M) (main M (cons rN rθ)))

{-
El : Ty → i★ → ★₁
El (σ ⇒ τ) Γ = ∀ {Δ} (Γ⊆Δ : Γ ⇴ Δ) → El σ Δ → El τ Δ

_⊢ᵥ_ : i★ → i★₁
Γ ⊢ᵥ τ = El τ Γ

⟨_⊢ᵥ⟩ : i★ → i★₁
⟨_⊢ᵥ⟩ = _⊢ᵥ_

Env : (Γ Δ : i★) → ★₁
Env Γ Δ = Γ ⇴₁ ⟨ Δ ⊢ᵥ⟩

ext : ∀ {Γ Δ Δ'} → Env Γ Δ → {!Δ ⇴ Δ'!} → ∀ {σ} → Δ' ⊢ᵥ σ → Env (Γ , σ) Δ'
ext ρ _ u here = {!!}
ext ρ _ u (there x) = {!!}

eval : ∀ {Γ Δ} → Env Γ Δ → ⟨ Γ ⊢⟩ ⇴₁ ⟨ Δ ⊢ᵥ⟩
eval ρ (V x) = ρ x
eval ρ (t · u) = eval ρ t (λ x → x) (eval ρ u)
eval ρ (ƛ t) = λ Γ⊆Δ x → eval (ext ρ {!Γ⊆Δ!} x) t
-}
-- -}
-- -}
-- -}
-- -}
-- -}
