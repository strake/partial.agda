module Function.Partial where

open import Level

open import Algebra.FunctionProperties.Core
open import Data.Bool
open import Data.Empty
open import Data.Maybe as Maybe
open import Data.Unit
open import Function hiding (id; _∘_)
import Function as F
open import Level using (Lift; lift)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq

infixr 1 _⇀_ _⇀'_
_⇀_ : {a b : _} (A : Set a) → (B : A → Set b) → Set (a ⊔ b)
A ⇀ B = (a : A) → Maybe (B a)

_⇀'_ : {ℓ : _} → Set ℓ → Set ℓ → Set ℓ
A ⇀' B = A ⇀ const B

infix 0 _≈_
_≈_ : {a b : _} {A : Set a} {B : A → Set b} → Rel (A ⇀ B) (a ⊔ b)
f ≈ g = ∀ a → f a ≡ g a

≈-isEquivalence : {a b : _} {A : Set a} {B : A → Set b} → IsEquivalence (_≈_ {A = A} {B = B})
≈-isEquivalence = record
    { refl = λ _ → refl;
      sym = F._∘_ PropEq.sym;
      trans = λ f≈g g≈h x → f≈g x ⟨ PropEq.trans ⟩ g≈h x }

dom : {a b : _} {A : Set a} {B : A → Set b} → (A ⇀ B) → A → Bool
dom = F._∘_ (maybe (const true) false)

id : {ℓ : _} {A : Set ℓ} → (A ⇀ const A)
id = just

∅ : {a b : _} {A : Set a} {B : A → Set b} → (A ⇀ B)
∅ _ = nothing

infixr 9 _∘_
_∘_ : {a b : _} {A : Set a} {B C : A → Set b} → (∀ {a} → B a ⇀' C a) → (A ⇀ B) → (A ⇀ C)
(f ∘ g) a = g a >>= f
  where open import Category.Monad
        open RawMonad Maybe.monad

join : {a b : _} {A : Set a} {B : A → Set b} → (∀ {a} → Op₂ (B a)) → Op₂ (A ⇀ B)
join _*_ f g a = just _*_ ⊛ f a ⊛ g a
  where open import Category.Monad
        open RawMonad Maybe.monad

_<|_ : {a b : _} {A : Set a} {B : A → Set b} → Op₂ (A ⇀ B)
_<|_ = join const

private _⊑M_ : {ℓ : _} {B : Set ℓ} → Rel (Maybe B) ℓ
just a  ⊑M just b  = a ≡ b
just _  ⊑M nothing = Lift ⊥
nothing ⊑M _       = Lift ⊤

infix 4 _⊑_
_⊑_ : {a b : _} {A : Set a} {B : A → Set b} → Rel (A ⇀ B) (a ⊔ b)
f ⊑ g = (a : _) → f a ⊑M g a

⊑-isPartialOrder : {a b : _} {A : Set a} {B : A → Set b} → IsPartialOrder {A = A ⇀ B} (_≈_ {A = A} {B = B}) (_⊑_ {A = A} {B = B})
⊑-isPartialOrder {A} {B} = record
    { isPreorder = record
          { isEquivalence = ≈-isEquivalence;
            reflexive = let ⊑M-refl : {ℓ : _} {A : Set ℓ} (a b : Maybe A) → a ≡ b → a ⊑M b
                            ⊑M-refl = λ { nothing  nothing  refl → lift tt;
                                          (just _) (just _) refl → refl }
                        in F._∘_ (⊑M-refl _ _);
            trans = λ {f} {g} {h} →
                      let ⊑M-trans : {ℓ : _} {A : Set ℓ} (x y z : Maybe A) →
                                     x ⊑M y → y ⊑M z → x ⊑M z
                          ⊑M-trans = λ { (just _) (just _) (just _) → PropEq.trans;
                                         (just _) (just _) nothing  → λ { _ (lift ()) };
                                         (just _) nothing  _        → λ { (lift ()) _ };
                                         nothing  _        _        → λ _ _ → lift tt }
                      in λ f⊑g g⊑h a → f⊑g a ⟨ ⊑M-trans (f a) (g a) (h a) ⟩ g⊑h a };
      antisym = let ⊑M-antisym : {ℓ : _} {A : Set ℓ} (x y : Maybe A) → x ⊑M y → y ⊑M x → x ≡ y
                    ⊑M-antisym = λ { (just _) (just _) refl _ → refl;
                                     (just _) nothing (lift ()) _;
                                     nothing (just _) _ (lift ());
                                     nothing nothing _ _ → refl }
                in λ f⊑g g⊑f a → f⊑g a ⟨ ⊑M-antisym _ _ ⟩ g⊑f a }
