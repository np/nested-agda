open import Type
open import Category.Applicative renaming (module RawApplicative to Applicative; RawApplicative to Applicative)
open import  Data.List using (List; []; _∷_; map)
open import  Data.Bool
open import  Data.Maybe.NP using (Maybe; nothing; just; maybe; maybe′; applicative)
open import  Data.Product using (_×_; _,_ ; proj₁ ; proj₂)
open import  Data.Star using (Star; ε) renaming (_◅_ to _∷_)
open import  Data.One
open import  Data.Zero
open import  Function.NP hiding (Π; _$_)
open import  Relation.Nullary
open import  Relation.Nullary.Decidable hiding (map)
open import  Relation.Binary hiding (_⇒_)
import       Relation.Binary.PropositionalEquality.NP as ≡
open         ≡ using (_≡_; _∙_; idp; !_; _≗_)
open import Level.NP
open import Scope

module Nested.PTS (Sort : ★) where

{-
post ICE ulate
  funext : ∀ {A : ★} {B : A → ★} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
-}

mutual
  Ty : ★ → ★
  Ty = Tm

  data Tm A : ★ where
    V   : (x : A) → Tm A
    ƛ   : (τ : Ty A) (t : Scope 𝟙 Tm A) → Tm A
    _·_ : (t u : Tm A) → Tm A
    Π   : (σ : Ty A) (τ : Scope 𝟙 Ty A) → Ty A
    `_  : (s : Sort) → Ty A

infixl 5 _·_

map™ : ∀ {A B} → (A → B) → Tm A → Tm B
map™ Δ (V x)   = V (Δ x)
map™ Δ (t · u) = map™ Δ t · map™ Δ u
map™ Δ (ƛ τ t) = ƛ (map™ Δ τ) (map™ (map▹ Δ) t)
map™ Δ (Π σ τ) = Π (map™ Δ σ) (map™ (map▹ Δ) τ)
map™ Δ (` κ)   = ` κ

map™-id : ∀ {A : ★} {f : A → A} → f ≗ id → map™ f ≗ id
map™-id Δ (V x) = ≡.cong V (Δ x)
map™-id Δ (ƛ τ t) = ≡.cong₂ ƛ (map™-id Δ τ) (map™-id (map▹-id Δ) t)
map™-id Δ (t · u) = ≡.cong₂ _·_ (map™-id Δ t) (map™-id Δ u)
map™-id Δ (Π σ τ) = ≡.cong₂ Π (map™-id Δ σ) (map™-id (map▹-id Δ) τ)
map™-id Δ (` s) = ≡.refl

map™-∘ : ∀ {A B C} {f : B → C} {g : A → B} {h : A → C} → h ≗ f ∘ g → map™ h ≗ map™ f ∘ map™ g
map™-∘ Δ (V x) = ≡.cong V (Δ x)
map™-∘ Δ (ƛ τ t) = ≡.cong₂ ƛ (map™-∘ Δ τ) (map™-∘ (map▹-∘ Δ) t)
map™-∘ Δ (t · u) = ≡.cong₂ _·_ (map™-∘ Δ t) (map™-∘ Δ u)
map™-∘ Δ (Π σ τ) = ≡.cong₂ Π (map™-∘ Δ σ) (map™-∘ (map▹-∘ Δ) τ)
map™-∘ Δ (` s) = ≡.refl

map™-∘′ : ∀ {A B C} (f : B → C) (g : A → B) → map™ (f ∘ g) ≗ map™ f ∘ map™ g
map™-∘′ f g = map™-∘ {f = f} {g} (λ _ → ≡.refl)

map™-ext : ∀ {A B} {f g : A → B} → f ≗ g → map™ f ≗ map™ g
map™-ext Δ (V x) = ≡.cong V (Δ x)
map™-ext Δ (ƛ τ t) = ≡.cong₂ ƛ (map™-ext Δ τ) (map™-ext (map▹-ext Δ) t)
map™-ext Δ (t · u) = ≡.cong₂ _·_ (map™-ext Δ t) (map™-ext Δ u)
map™-ext Δ (Π σ τ) = ≡.cong₂ Π (map™-ext Δ σ) (map™-ext (map▹-ext Δ) τ)
map™-ext Δ (` s) = ≡.refl

_→™_ : ★ → ★ → ★
A →™ B = Tm A → Tm B

-- Substitutions
_⇶_ : ★ → ★ → ★
A ⇶ B = A → Tm B

⇑™ : ∀ {A B} → A ⇶ B → (A ▹ 𝟙) ⇶ (B ▹ 𝟙)
(⇑™ θ) (new x) = V (new x)
(⇑™ θ) (old x) = map™ old (θ x)

⇑™-V : ∀ {A} {Δ : A ⇶ A} → Δ ≗ V → ⇑™ Δ ≗ V
⇑™-V Δᵣ (new x) = ≡.refl
⇑™-V Δᵣ (old x) = ≡.cong (map™ old) (Δᵣ x)

⇑™-ext : ∀ {A B} {f g : A ⇶ B} → f ≗ g → ⇑™ f ≗ ⇑™ g
⇑™-ext f≗g (old x) = ≡.cong (map™ old) (f≗g x)
⇑™-ext f≗g (new x) = ≡.refl

_=<<_ : ∀ {A B} → (A ⇶ B) → Tm A → Tm B
Δ =<< (V x)   = Δ x
Δ =<< (t · u) = Δ =<< t · Δ =<< u
Δ =<< (ƛ τ t) = ƛ (Δ =<< τ) (⇑™ Δ =<< t)
Δ =<< (Π σ τ) = Π (Δ =<< σ)  (⇑™ Δ =<< τ)
Δ =<< (` κ)   = ` κ

=<<-ext : ∀ {A B} {f g : A ⇶ B} → f ≗ g → _=<<_ f ≗ _=<<_ g
=<<-ext Δ (V x) = Δ x
=<<-ext Δ (ƛ τ t) = ≡.cong₂ ƛ (=<<-ext Δ τ) (=<<-ext (⇑™-ext Δ) t)
=<<-ext Δ (t · u) = ≡.cong₂ _·_ (=<<-ext Δ t) (=<<-ext Δ u)
=<<-ext Δ (Π σ τ) = ≡.cong₂ Π (=<<-ext Δ σ) (=<<-ext (⇑™-ext Δ) τ)
=<<-ext Δ (` s) = ≡.refl

_<=<_ : ∀ {A B C} → B ⇶ C → A ⇶ B → A ⇶ C
(f <=< g) x = f =<< g x

join™ : ∀ {A} → Tm (Tm A) → Tm A
join™ = _=<<_ id

⇑™-⇑™∘map▹ : ∀ {A B C} {f : B ⇶ C} {g : A → B} {h : A ⇶ C} → h ≗ f ∘ g → ⇑™ h ≗ ⇑™ f ∘ map▹ g
⇑™-⇑™∘map▹ Δ (new x) = ≡.refl
⇑™-⇑™∘map▹ Δ (old x)   = ≡.cong (map™ old) (Δ x)

⇑™-map▹∘⇑™ : ∀ {A B C} {f : B → C} {g : A ⇶ B} {h : A ⇶ C} → h ≗ map™ f ∘ g → ⇑™ h ≗ map™ (map▹ f) ∘ ⇑™ g
⇑™-map▹∘⇑™ Δ (new x) = ≡.refl
⇑™-map▹∘⇑™ Δ (old x) = ≡.cong (map™ old) (Δ x) ∙ !(map™-∘′ old _ _) ∙ map™-∘′ (map▹ _) old _

=<<-=<<∘map™ : ∀ {A B C} {f : B ⇶ C} {g : A → B} {h : A ⇶ C} → h ≗ f ∘ g → _=<<_ h ≗ _=<<_ f ∘ map™ g
=<<-=<<∘map™ Δ (V x) = Δ x
=<<-=<<∘map™ Δ (ƛ τ t) = ≡.cong₂ ƛ (=<<-=<<∘map™ Δ τ) (=<<-=<<∘map™ (⇑™-⇑™∘map▹ Δ) t)
=<<-=<<∘map™ Δ (t · u) = ≡.cong₂ _·_ (=<<-=<<∘map™ Δ t) (=<<-=<<∘map™ Δ u)
=<<-=<<∘map™ Δ (Π σ τ) = ≡.cong₂ Π (=<<-=<<∘map™ Δ σ) (=<<-=<<∘map™ (⇑™-⇑™∘map▹ Δ) τ)
=<<-=<<∘map™ Δ (` s) = ≡.refl

=<<-=<<∘map™′ : ∀ {A B C} (f : B ⇶ C) (g : A → B) → _=<<_ (f ∘ g) ≗ _=<<_ f ∘ map™ g
=<<-=<<∘map™′ f g = =<<-=<<∘map™ {f = f} {g} λ _ → ≡.refl

join∘map : ∀ {A B} (f : A ⇶ B) → join™ ∘ map™ f ≗ _=<<_ f
join∘map f = !_ ∘ =<<-=<<∘map™′ id f

=<<-map™∘=<< : ∀ {A B C} {f : B → C} {g : A ⇶ B} {h : A ⇶ C} → h ≗ map™ f ∘ g → _=<<_ h ≗ map™ f ∘ _=<<_ g
=<<-map™∘=<< Δ (V x) = Δ x
=<<-map™∘=<< Δ (ƛ τ t) = ≡.cong₂ ƛ (=<<-map™∘=<< Δ τ) (=<<-map™∘=<< (⇑™-map▹∘⇑™ Δ) t)
=<<-map™∘=<< Δ (t · u) = ≡.cong₂ _·_ (=<<-map™∘=<< Δ t) (=<<-map™∘=<< Δ u)
=<<-map™∘=<< Δ (Π σ τ) = ≡.cong₂ Π (=<<-map™∘=<< Δ σ) (=<<-map™∘=<< (⇑™-map▹∘⇑™ Δ) τ)
=<<-map™∘=<< Δ (` s) = ≡.refl

=<<-map™∘=<<′ : ∀ {A B C} (f : B → C) (g : A ⇶ B) → _=<<_ (map™ f ∘ g) ≗ map™ f ∘ _=<<_ g
=<<-map™∘=<<′ f g = =<<-map™∘=<< {f = f} {g} (λ _ → ≡.refl)

⇑™-∘ : ∀ {A B C} {f : B ⇶ C} {g : A ⇶ B} {h : A ⇶ C} → h ≗ f <=< g → ⇑™ h ≗ ⇑™ f <=< ⇑™ g
⇑™-∘ Δᵣ (new x) = ≡.refl
⇑™-∘ {g = g} Δᵣ (old x) = ≡.cong (map™ old) (Δᵣ x) ∙ ! =<<-map™∘=<<′ old _ (g x) ∙ =<<-=<<∘map™′ _ old (g x)

V=<< : ∀ {A} {Δ : A ⇶ A} → Δ ≗ V → _=<<_ Δ ≗ id
V=<< Δᵣ (V x) = Δᵣ x
V=<< Δᵣ (ƛ τ t) = ≡.cong₂ ƛ (V=<< Δᵣ τ) (V=<< (⇑™-V Δᵣ) t)
V=<< Δᵣ (t · u) = ≡.cong₂ _·_ (V=<< Δᵣ t) (V=<< Δᵣ u)
V=<< Δᵣ (Π σ τ) = ≡.cong₂ Π (V=<< Δᵣ σ) (V=<< (⇑™-V Δᵣ) τ)
V=<< Δᵣ (` s) = ≡.refl

=<<-∘ : ∀ {A B C} {f : B ⇶ C} {g : A ⇶ B} {h : A ⇶ C} → h ≗ f <=< g → _=<<_ h ≗ _=<<_ f ∘ _=<<_ g
=<<-∘ Δ (V x) = Δ x
=<<-∘ Δ (ƛ τ t) = ≡.cong₂ ƛ (=<<-∘ Δ τ) (=<<-∘ (⇑™-∘ Δ) t)
=<<-∘ Δ (t · u) = ≡.cong₂ _·_ (=<<-∘ Δ t) (=<<-∘ Δ u)
=<<-∘ Δ (Π σ τ) = ≡.cong₂ Π (=<<-∘ Δ σ) (=<<-∘ (⇑™-∘ Δ) τ)
=<<-∘ Δ (` s) = ≡.refl

=<<V : ∀ {A B} (f : A → Tm B) → _=<<_ f ∘ V ≗ f
=<<V  _ _ = ≡.refl

[0≔_] : ∀ {A} → Tm A → (A ▹ 𝟙) ⇶ A
[0≔ u ] (new x) = u
[0≔ u ] (old x) = V x

map™∘[0:=] : ∀ {A B} τ (f : A → B) → map™ f ∘ [0≔ τ ] ≗ [0≔ map™ f τ ] ∘ map▹ f
map™∘[0:=] _ _ (old x) = ≡.refl
map™∘[0:=] _ _ (new x) = ≡.refl

_$_ : ∀ {A} → Tm (A ▹ 𝟙) → Tm A → Tm A
t $ u = [0≔ u ] =<< t

map™-$ : ∀ {A B} (f : A → B) σ τ → map™ f (σ $ τ) ≡ (map™ (map▹ f) σ $ map™ f τ)
map™-$ f σ τ = !(=<<-map™∘=<<′ f [0≔ τ ] σ) ∙ =<<-ext (map™∘[0:=] τ f) σ ∙ =<<-=<<∘map™′ [0≔ map™ f τ ] (map▹ f) σ

abs™ : ∀ {A} → ∀Scope𝟙 Tm A → Scope 𝟙 Tm A
abs™ = abs {Tm}

data Cx : ★ → ★₁ where
  ε    : Cx 𝟘
  _,,_ : ∀ {A}
           (Γ : Cx A)
           (τ : Ty A)
         → Cx (A ▹ 𝟙)

data ⟨_∶_⟩∈_ : ∀ {A} (x : A) (τ : Ty A) (Γ : Cx A) → ★₁ where

  here' : ∀ {B} {x : B ▹ 𝟙} {τ : Ty (B ▹ 𝟙)} {τ' Γ}
           (τ≅τ' : τ ≡ map™ old τ')
         →         -----------------------
                   ⟨ x ∶ τ ⟩∈ (Γ ,, τ')

  there' : ∀ {B} {τ : Ty (B ▹ 𝟙)} {x τ' σ Γ}
             (τ≅τ' :  τ ≡ map™ old τ'         )
             (x∶τ∈Γ : ⟨ x ∶ τ' ⟩∈ Γ           )
           →          ------------------------
                      ⟨ old x ∶ τ ⟩∈ (Γ ,, σ)

here : ∀ {A τ x} {Γ : Cx A}
       → ⟨ x ∶ map™ old τ ⟩∈ (Γ ,, τ)
here = here' ≡.refl

there : ∀ {A} {x : A} {τ σ} {Γ : Cx A}
          (x∶τ∈Γ : ⟨ x ∶ τ ⟩∈ Γ                   )
        →          ---------------------------------
                   ⟨ old x ∶ map™ old τ ⟩∈ (Γ ,, σ)
there = there' ≡.refl

module _ {A B} where
    _→[_]⊢_ : Cx A → (A → B) → Cx B → ★₁
    Γ →[ f ]⊢ Δ = ∀ {x τ} → ⟨ x ∶ τ ⟩∈ Γ → ⟨ f x ∶ map™ f τ ⟩∈ Δ

map,, : ∀ {A B Γ Δ τ}{f : A → B} → (Γ →[ f ]⊢ Δ) → (Γ ,, τ) →[ map▹ f ]⊢ (Δ ,, map™ f τ)
map,, {τ = τ} {f} φ (here' ≡.refl) = here' (!(map™-∘′ (map▹ f) old τ) ∙ map™-∘′ old f τ)
map,, {f = f} φ (there' {τ' = τ'} ≡.refl x∈) = there' (!(map™-∘′ (map▹ f) old τ') ∙ map™-∘′ old f τ') (φ x∈)

module Typing
    (_∶κ_      : (s₁ s₂ : Sort) → ★)
    (⟨_,_,_⟩∈R : (s₁ s₂ s₃ : Sort) → ★)
  where

  infix 2 _⊢_∶_

  data _⊢_∶_ {A} (Γ : Cx A) : Tm A → Ty A → ★₁ where

    V : ∀ {x τ}
          (x∈Γ : ⟨ x ∶ τ ⟩∈ Γ)
        →        -------------
                  Γ ⊢ V x ∶ τ

    ƛ : ∀ {σ τ s t}
          (⊢Π : Γ ⊢ Π σ τ ∶ ` s          )
          (⊢t : (Γ ,, σ) ⊢ t ∶ τ         )
         →      --------------------------
                 Γ ⊢ ƛ σ t ∶ Π σ τ

    _·_  : ∀ {σ τ t u}
             (⊢t : Γ ⊢ t ∶ Π σ τ     )
             (⊢u : Γ ⊢ u ∶ σ         )
           →     ---------------------------
                    Γ ⊢ t · u ∶ τ $ σ

    Π : ∀ {σ τ s₁ s₂ s₃}
          (s∈ : ⟨ s₁ , s₂ , s₃ ⟩∈R   )
          (⊢σ : Γ ⊢ σ        ∶ ` s₁  )
          (⊢τ : (Γ ,, σ) ⊢ τ ∶ ` s₂  )
         →      -----------------------
                  Γ ⊢ Π σ τ ∶ ` s₃

    `_ : ∀ {s₁ s₂}
           (s₁∶s₂ : s₁ ∶κ s₂        )
         →       ------------------
                   Γ ⊢ ` s₁ ∶ ` s₂

  map⊢ : ∀ {A B Γ Δ τ t} {f : A → B} (f⊢ : Γ →[ f ]⊢ Δ) → Γ ⊢ t ∶ τ → Δ ⊢ map™ f t ∶ map™ f τ
  map⊢ f⊢ (V x)     = V (f⊢ x)
  map⊢ {A} {B} {Γ} {Δ} {f = f} f⊢ (_·_ {σ} {τ} {t} {u} t⊢ u⊢) =
     ≡.subst (λ x → Δ ⊢ map™ f t · map™ f u ∶ x) (≡.sym (map™-$ f τ σ)) (map⊢ f⊢ t⊢ · map⊢ f⊢ u⊢)
  map⊢ f⊢ (ƛ τ t)   = ƛ (map⊢ f⊢ τ) (map⊢ (map,, f⊢) t)
  map⊢ f⊢ (Π r σ τ) = Π r (map⊢ f⊢ σ) (map⊢ (map,, f⊢) τ)
  map⊢ f⊢ (` κ)     = ` κ

  module _ {A B} where
    _⇶[_]⊢_ : Cx A → (A ⇶ B) → Cx B → ★₁
    Γ ⇶[ f ]⊢ Δ = ∀ {x τ} → ⟨ x ∶ τ ⟩∈ Γ → Δ ⊢ f x ∶ f =<< τ

    {-
  module _ {A B} where
    ⇑⊢ : {f : A ⇶ B} {Γ : Cx A} {Δ : Cx B} {τ : _} → Γ ⇶[ f ]⊢ Δ → (Γ ,, τ) ⇶[ ⇑™ f ]⊢ (Δ ,, (f =<< τ))
    ⇑⊢ θ (here' ≡.refl) = {!V ?!}
    ⇑⊢ θ (there' ≡.refl x₁) = {!map⊢ ? (θ x₁)!} -- map⊢ {!!} {!θ x₁!}
    -}
-- -}
-- -}
-- -}
-- -}
