module NestedSeqCal where

open import Type
open import Data.One
open import Function.NP
open import Scope

---- o : type.
data ο : ★ where
  ---- imp : o -> o -> o.
  _⇒_ : ο → ο → ο
  ---- top : o.
  ⊤ : ο
open IndexedScope1 {ο}

---- hyp : o -> type.
data Hyp (Γ : ο → ★) : ο → ★ where
  var : ∀ {A} → Γ A → Hyp Γ A

record [Hyp_⇒_·_] (A : ο) (F : (ο → ★) → (ο → ★)) (B : ο) (Γ : ο → ★) : ★ where
  constructor mk
  field
    out : F (Γ , A) B
open [Hyp_⇒_·_]

infixl 4 _∙_
_∙_ : ∀ {Γ A B F} → [Hyp A ⇒ F · B ] Γ → (Hyp Γ A → F Γ B)
x ∙ y = {!x >>= [0≔ y ]!}

abs : ∀ {Γ A B F} → (Hyp Γ A → F Γ B) → [Hyp A ⇒ F · B ] Γ
abs x = {!!}

[Hyp_⇒Hyp_⇒_·_] : ο → ο → ((ο → ★) → (ο → ★)) → ο → (ο → ★) → ★
[Hyp A ⇒Hyp B ⇒ F · C ] Γ = [Hyp A ⇒ (λ Δ C → [Hyp B ⇒ F · C ] Δ) · C ] Γ

---- conc : o -> type.
data Conc Γ : ο → ★ where
  ---- init : hyp A -> conc A
  init : ∀ {A} → Hyp Γ A → Conc Γ A
  ---- impr : (hyp A -> conc B) -> conc (imp A B).
  ⇒ᵣ : ∀ {A B} → [Hyp A ⇒ Conc · B ] Γ → Conc Γ (A ⇒ B)
  ---- impl : hyp (imp A B) -> conc A -> (hyp A -> conc C) -> conc C
  ⇒ₗ : ∀ {A B C} → Conc Γ A → [Hyp B ⇒ Conc · C ] Γ → Hyp Γ (A ⇒ B) → Conc Γ C
  ---- topr : conc top.
  ⊤ᵣ : Conc Γ ⊤

wkHyp : ∀ {A B Γ} → Hyp Γ A → [Hyp B ⇒ Hyp · A ] Γ
wkHyp = {!!}

wk : ∀ {A B Γ} → Conc Γ A → [Hyp B ⇒ Conc · A ] Γ
wk = {!!}

---- cut : conc A -> (hyp A -> conc C) -> conc C -> type.
data Cut {Γ} : ∀ A {C} → Conc Γ A → [Hyp A ⇒ Conc · C ] Γ → Conc Γ C → ★ where
  ---- initD : cut A (init Ha) ([Ha] E Ha) (E Ha).
  initD : ∀ {A B Hₐ} {E : [Hyp A ⇒ Conc · B ] Γ} → Cut _ (init Hₐ) E (E ∙ Hₐ)
  ---- initE : cut A D ([Ha] init Ha) D.
  initE : ∀ {A D} → Cut A D (abs init) D

  ---- closed : cut A D ([Ha] E') E'.
  closed : ∀ {A C D E} → Cut A {C} D (wk E) E

  ---- impC : cut (imp A B) (impR ([Ha] D' Ha))
  ----           ([Hab] impL (E1 Hab : conc A) ([Hb] E2 Hab Hb : conc C) Hab)
  ----           F
  ----    <- cut (imp A B) (impR D') E1 (F1 : conc A)
  ----    <- ({Hb:hyp B} cut (imp A B) (impR D') ([Hab] E2 Hab Hb) (F2 Hb : conc C))
  ----    <- cut A F1 D' (F3 : conc B)
  ----    <- cut B F3 F2 F.
  impC : ∀ {A B C F F1 F2 F3 D'} {E1 : [Hyp (A ⇒ B) ⇒ Conc · A ] Γ} {E2 : [Hyp (A ⇒ B) ⇒Hyp B ⇒ Conc · C ] Γ}
         → Cut B F3 F2 F
         → Cut A F1 D' F3
         → ({Hb : Hyp Γ B} → Cut (A ⇒ B) (⇒ᵣ D') (abs (λ Hab → E2 ∙ Hab ∙ Hb)) (F2 ∙ Hb))
         → Cut (A ⇒ B) (⇒ᵣ D') E1 F1
         → Cut (A ⇒ B) (⇒ᵣ D') (abs (λ Hab → ⇒ₗ (E1 ∙ Hab) (E2 ∙ Hab) Hab)) F

---- impLLC : cut A (impL D1 ([Hb] D2 Hb) Hi) E
----                (impL D1 F2 Hi)
----          <- ({Hb} cut A (D2 Hb) E (F2 Hb)).
  impLLC : ∀ {A B D2 E F2 D1 Hi}
           → ((Hb : Hyp Γ B) → Cut A {B} (D2 ∙ Hb) E (F2 ∙ Hb))
           → Cut A {B} (⇒ₗ {_} {A {- not sure-}} {B {-not sure-}} {_} D1 D2 Hi) E (⇒ₗ D1 F2 Hi)

  ---- impLRC : cut A (D : conc A) ([Ha] impL (E1 Ha) ([Hb] E2 Ha Hb) Hi)
  impLRC : ∀ {A B D E1} {E2 : [Hyp A ⇒Hyp B ⇒ Conc · _ ] Γ} {Hi F1 F2}
           → ({Hb : _} → Cut A {B} D (abs (λ Ha → E2 ∙ Ha ∙ Hb)) (F2 ∙ Hb))
           → Cut A {B} D E1 F1
           → Cut A {_} D (abs (λ Ha → ⇒ₗ {_} {B{-not sure-}} (E1 ∙ Ha) (E2 ∙ Ha) Hi)) (⇒ₗ F1 F2 Hi)

  ---- impRRC : cut A D ([Ha] impR ([H1] E1 Ha H1)) (impR ([H1] F1 H1))
  ----       <- ({H1} cut A D ([Ha] E1 Ha H1) (F1 H1)).
  impRRC : ∀ {A B D} {E1 : [Hyp A ⇒Hyp _ ⇒ Conc · _ ] _} {F1}
           → ({H1 : _} → Cut A {B} D (abs λ Ha → E1 ∙ Ha ∙ H1) (F1 ∙ H1))
           → Cut A D (abs λ Ha → ⇒ᵣ {_} {A{-not sure-}} (abs λ H1 → E1 ∙ Ha ∙ H1)) (⇒ᵣ F1)

cut : ∀ {Γ} A {B} → Conc Γ A → [Hyp A ⇒ Conc · B ] Γ → Conc Γ B
cut A (init x)         f = f ∙ x
cut A cA (mk (init (var here))) = cA
cut A cA (mk (init (var (there x)))) = init (var x) -- not part of the Cut type
cut A (⇒ₗ D1 D2 Hi) E = ⇒ₗ D1 (abs λ Hb → cut A (D2 ∙ Hb) E) Hi
cut A D (mk (⇒ᵣ E1)) = ⇒ᵣ (abs λ Ha1 → cut A D (mk (E1 ∙ out (wkHyp Ha1))))
{-
         → Cut B F3 F2 F
         → Cut A F1 D' F3
         → ({Hb : Hyp Γ B} → Cut (A ⇒ B) (⇒ᵣ D') (abs (λ Hab → E2 ∙ Hab ∙ Hb)) (F2 ∙ Hb))
         → Cut (A ⇒ B) (⇒ᵣ D') E1 F1
         → Cut (A ⇒ B) (⇒ᵣ D') (abs (λ Hab → ⇒ₗ (E1 ∙ Hab) (E2 ∙ Hab) Hab)) F
         -}
cut {Γ} (A ⇒ B) {B'} (⇒ᵣ D') (mk (⇒ₗ E1 E2 (var here))) = cut B (cut A (cut (A ⇒ B) (⇒ᵣ D') (mk E1)) D')
          (abs λ Hb → _∙_ {Γ} {B} {_} {_} (mk {B} {λ Γ → Conc {!(Γ , ?)!}} {{!!}} {Γ} (cut {Γ} (A ⇒ B) {B'} (⇒ᵣ {Γ} {A} {B} D') (mk (_∙_ {Γ , (A ⇒ B)} {B} {B'} {Conc} E2 (out (wkHyp {B} {A ⇒ B} {Γ} Hb)))))) Hb)
cut A D (mk (⇒ₗ E1 E2 (var (there Hi)))) = ⇒ₗ (cut A D (mk E1)) (abs λ Hb → cut A D (mk (E2 ∙ out (wkHyp Hb)))) (var Hi)
-- 
{-
  ({Hb : _} → Cut A {B} D (abs (λ Ha → E2 ∙ Ha ∙ Hb)) (F2 ∙ Hb))
  Cut A {B} D E1 F1
  Cut A {_} D (abs (λ Ha → ⇒ₗ {_} {B{-not sure-}} (E1 ∙ Ha) (E2 ∙ Ha) Hi)) (⇒ₗ F1 F2 Hi)
-}
cut A D (mk ⊤ᵣ) = ⊤ᵣ
--cut ⊤ᵣ f = {!!}

{-
{-
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

i★ : ★ → ★₁
i★ A = A → Ty → ★

{-
i★₁ : Set₂
i★₁ = Ty → ★₁

_⇴_ : ∀ {A} → i★ A → i★ A → ★
F ⇴ G = ∀ {i j} → F i j → G i j

_⇴₁_ : i★ → i★₁ → ★₁
F ⇴₁ G = ∀ {i} → F i → G i
-}

_∶_∈_ : ∀ {A} → A → Ty → i★ A → ★
x ∶ τ ∈ Γ = Γ x τ

data _,_⇒_ {A} {B} (Γ : i★ A) τ (Δ : i★ B) : i★ (A ▹ B) where
  here   : ∀ {x}   → x ∶ τ ∈ Δ → new x ∶ τ ∈ (Γ , τ ⇒ Δ)
  there  : ∀ {x σ} → x ∶ σ ∈ Γ → old x ∶ σ ∈ (Γ , τ ⇒ Δ)

{-
data _,_ {A} (Γ : i★ A) τ : i★ (A ▹ 𝟙) where
  here  : new _ ∶ τ ∈ (Γ , τ)
  there  : ∀ {x σ} → x ∶ σ ∈ Γ → old x ∶ σ ∈ (Γ , τ)
-}

-- i★𝟙 : i★ 𝟙
-- i★𝟙 _ _ = 𝟙
record i★𝟙 (_ : 𝟙) (_ : Ty) : ★ where
  constructor 0'

_,_ : ∀ {A} (Γ : i★ A) τ → i★ (A ▹ 𝟙)
Γ , τ = Γ , τ ⇒ i★𝟙

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

∀Scope : (★ → ★) → ★ → ★₁
∀Scope F A = ∀ {B} → B → F (A ▹ B)
⊢ƛ : ∀ {A} {f : ∀Scope Tm A} {Γ} {σ τ} → (∀ {B} {x : B} {Δ : i★ B} → x ∶ σ ∈ Δ → (Γ , σ ⇒ Δ) ⊢ f x ∶ τ) → (Γ , σ) ⊢ f 0' ∶ τ
⊢ƛ ⊢f = ⊢f 0'

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

module Subst™ where
  [_] : ∀ {A B} → A ⇶ B → A →™ B
  [ θ ](V x)   = θ x
  [ θ ](t · u) = [ θ ] t · [ θ ] u
  [ θ ](ƛ t)   = ƛ ([ ⇑™ θ ] t)

join™ : ∀ {A} → Tm (Tm A) → Tm A
join™ = Subst™.[ id ]

_>>=™_ : ∀ {A B} → Tm A → (A → Tm B) → Tm B
t >>=™ f = Subst™.[ f ] t

[0≔_] : ∀ {A} → Tm A → A ▹ 𝟙 → Tm A
[0≔ u ] (new x) = u
[0≔ u ] (old x) = V x

_∙_ : ∀ {A} → Tm (A ▹ 𝟙) → Tm A → Tm A
t ∙ u = t >>=™ [0≔ u ]

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
