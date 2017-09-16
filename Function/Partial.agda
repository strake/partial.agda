open import Agda.Primitive

module Function.Partial {ℓ : Level} where

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
_⇀_ : (A : Set ℓ) → (B : A → Set ℓ) → Set ℓ
A ⇀ B = (a : A) → Maybe (B a)

_⇀'_ : Set ℓ → Set ℓ → Set ℓ
A ⇀' B = A ⇀ const B

infix 0 _≈_
_≈_ : ∀ {A B} → Rel (A ⇀ B) ℓ
f ≈ g = ∀ a → f a ≡ g a

≈-isEquivalence : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
≈-isEquivalence = record
    { refl = λ _ → refl;
      sym = F._∘_ PropEq.sym;
      trans = λ f≈g g≈h x → f≈g x ⟨ PropEq.trans ⟩ g≈h x }

dom : ∀ {A B} → (A ⇀ B) → A → Bool
dom = F._∘_ (maybe (const true) false)

id : ∀ {A} → (A ⇀ const A)
id = just

∅ : ∀ {A B} → (A ⇀ B)
∅ _ = nothing

infixr 9 _∘_
_∘_ : ∀ {A B C} → (∀ {a} → B a ⇀' C a) → (A ⇀ B) → (A ⇀ C)
(f ∘ g) a = g a >>= f
  where open import Category.Monad
        open RawMonad Maybe.monad

join : ∀ {A B} → (∀ {a} → Op₂ (B a)) → Op₂ (A ⇀ B)
join _*_ f g a = just _*_ ⊛ f a ⊛ g a
  where open import Category.Monad
        open RawMonad Maybe.monad

_<|_ : ∀ {A B} → Op₂ (A ⇀ B)
_<|_ = join const

private _⊑M_ : ∀ {B} → Rel (Maybe B) ℓ
just a  ⊑M just b  = a ≡ b
just _  ⊑M nothing = Lift ⊥
nothing ⊑M _       = Lift ⊤

infix 4 _⊑_
_⊑_ : ∀ {A B} → Rel (A ⇀ B) ℓ
f ⊑ g = (a : _) → f a ⊑M g a

⊑-isPartialOrder : ∀ {A B} → IsPartialOrder {A = A ⇀ B} (_≈_ {A} {B}) (_⊑_ {A} {B})
⊑-isPartialOrder {A} {B} = record
    { isPreorder = record
          { isEquivalence = ≈-isEquivalence;
            reflexive = let ⊑M-refl : {A : Set ℓ} (a b : Maybe A) → a ≡ b → a ⊑M b
                            ⊑M-refl = λ { nothing  nothing  refl → lift tt;
                                          (just _) (just _) refl → refl }
                        in F._∘_ (⊑M-refl _ _);
            trans = λ {f} {g} {h} →
                      let ⊑M-trans : {A : Set ℓ} (x y z : Maybe A) →
                                     x ⊑M y → y ⊑M z → x ⊑M z
                          ⊑M-trans = λ { (just _) (just _) (just _) → PropEq.trans;
                                         (just _) (just _) nothing  → λ { _ (lift ()) };
                                         (just _) nothing  _        → λ { (lift ()) _ };
                                         nothing  _        _        → λ _ _ → lift tt }
                          ⊑-trans : (f g h : A ⇀ B) → f ⊑ g → g ⊑ h → f ⊑ h
                          ⊑-trans f g h f⊑g g⊑h a = f⊑g a ⟨ ⊑M-trans (f a) (g a) (h a) ⟩ g⊑h a
                      in ⊑-trans f g h };
      antisym = let ⊑M-antisym : {A : Set ℓ} (x y : Maybe A) → x ⊑M y → y ⊑M x → x ≡ y
                    ⊑M-antisym = λ { (just _) (just _) refl _ → refl;
                                     (just _) nothing (lift ()) _;
                                     nothing (just _) _ (lift ());
                                     nothing nothing _ _ → refl }
                in λ f⊑g g⊑f a → f⊑g a ⟨ ⊑M-antisym _ _ ⟩ g⊑f a }
