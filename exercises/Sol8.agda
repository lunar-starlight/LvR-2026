---------------------------------------------------------------------------
-- Week 8 exercises for the Logika v računalništvu course at UL FMF      --
-- Lecturer: Alex Simpson                                                --
-- Teaching Assistant: Luna Strah                                        --
--                                                                       --
-- Adapted from Danel Ahmans's exercises from 2022 available at:         --
-- https://github.com/danelahman/lograc-2022/blob/main/exercises/        --
--                                                                       --
-- Course website: https://ucilnica.fmf.uni-lj.si/course/view.php?id=252 --
---------------------------------------------------------------------------

module Sol8 where

open import Data.Empty           using (⊥; ⊥-elim)
open import Data.Fin             using (Fin; zero; suc)
open import Data.List            using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (map-id; map-compose)
open import Data.Maybe           using (Maybe; nothing; just)
open import Data.Nat             using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties  using (+-identityˡ; +-identityʳ; +-suc; +-comm)
open import Data.Product         using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.Vec             using (Vec; []; _∷_)

open import Function             using (id; _∘_)

open import Relation.Nullary     using (¬_)

import Relation.Binary.PropositionalEquality as Eq
open Eq                          using (_≡_; refl; sym; trans; cong; subst)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

----------------
-- Exercise 1 --
----------------

{-
   Here's the safe lookup function for lists (in terms of the `<` relation).
-}

safe-list-lookup : {A : Set} → (xs : List A) → (i : ℕ) → i < length xs → A
safe-list-lookup (x ∷ xs) zero    (s≤s p) = x
safe-list-lookup (x ∷ xs) (suc i) (s≤s p) = safe-list-lookup xs i p

{-
   Establish the extensionality principle for lists: if two equal-length lists
   are index-wise equal, then these two lists are themselves equal.

   Use equational reasoning as laid out below. This allows you to work on an
   equality in steps. For more details you can look at the implementation below
   or online resources posted on the course page.
-}

module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 step-≡-∣ step-≡-⟩
  infix  3 _∎

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin x≡y  =  x≡y

  step-≡-∣ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
  step-≡-∣ x x≡y  =  x≡y

  step-≡-⟩ : ∀ (x : A) {y z : A} → y ≡ z → x ≡ y → x ≡ z
  step-≡-⟩ x y≡z x≡y  =  trans x≡y y≡z

  syntax step-≡-∣ x x≡y      =  x ≡⟨⟩ x≡y
  syntax step-≡-⟩ x y≡z x≡y  =  x ≡⟨  x≡y ⟩ y≡z

  _∎ : ∀ (x : A) → x ≡ x
  x ∎  =  refl

open ≡-Reasoning

list-ext : {A : Set} {xs ys : List A}
         → length xs ≡ length ys
         → ((i : ℕ) → (p : i < length xs) → (q : i < length ys)
              → safe-list-lookup xs i p ≡ safe-list-lookup ys i q)
         → xs ≡ ys

list-ext {xs = []} {[]} _ _ = refl
list-ext {xs = x ∷ xs} {y ∷ ys} h g =
   begin
     x ∷ xs
   ≡⟨ cong (_∷ xs) (g 0 (s≤s z≤n) (s≤s z≤n)) ⟩
     y ∷ xs
   ≡⟨ cong (y ∷_) (list-ext (suc-inj h) λ i p q → g (suc i) (s≤s p) (s≤s q)) ⟩
     y ∷ ys
   ∎
   where
      suc-inj : {n m : ℕ} → (suc n) ≡ (suc m) → n ≡ m
      suc-inj refl = refl

{-
   Notice that we have generalised this statement a bit compared to what one
   would have likely written down in the first place.

   Namely, when comparing the values of the lists index-wise, we require
   separate proofs that `i < length xs` and `i < length ys` despite knowing that
   `length xs ≡ length ys`. We have done this to avoid having to use `subst` to
   fix the argument types in one of the applications of `safe-list-lookup`. If
   we would have used `subst` to fix the arguments, then we could have run into
   difficulties such as having to additionally push `subst` through
   constructors.
-}





----------------
-- Exercise 2 --
----------------

{-
   Next, we revisit another exercise from last week. This one was about
   translating a vector to a list.

   Differently from last week, we will use the `Σ`-type to encforce it in
   `vec-list-Σ`'s type that the returned list has the same length as the
   given vector. Recall that last week we were doing this extrinsically
   by proving an auxiliary equational lemma **after** defining `vec-list`.
-}

vec-list-Σ : {A : Set} {n : ℕ} → Vec A n → Σ[ xs ∈ List A ] (length xs ≡ n)
vec-list-Σ [] = [] , refl
vec-list-Σ (x ∷ xs) = x ∷ proj₁ (vec-list-Σ xs) , cong suc (proj₂ (vec-list-Σ xs))


----------------
-- Exercise 3 --
----------------

{-
   Recall that an isomorphism is a map `f` together with an 'inverse map `f⁻¹`',
   such that the composites of these maps are the identity map.
-}

infix 0 _≃_

record _≃_ (A B : Set) : Set where         -- unicode `≃` with `\~-`
  field
    to      : A → B
    from    : B → A
    from∘to : (x : A) → from (to x) ≡ x
    to∘from : (y : B) → to (from y) ≡ y

open _≃_

{-
   Prove that the `Σ`-type is associative as a type former. For this, prove an
   isomorphism between the two different ways of associating `Σ`.
-}

{-
   First, prove this by constructing the isomorphism using the (old-school,
   functional programming style) `record { ... ; field = ... ; ... }` syntax.
-}

Σ-assoc : {A : Set} {B : A → Set} {C : (x : A) → B x → Set}
        → Σ[ x ∈ A ] (Σ[ y ∈ B x ] (C x y))
          ≃
          Σ[ xy ∈ Σ[ x ∈ A ] (B x) ] (C (proj₁ xy) (proj₂ xy))

Σ-assoc = record
  { to = λ z → (z .proj₁ , z .proj₂ .proj₁) , z .proj₂ .proj₂
  ; from = λ z → proj₁ (z .proj₁) , proj₂ (z .proj₁) , z .proj₂
  ; from∘to = λ _ → refl
  ; to∘from = λ _ → refl }

{-
   Second, prove the same thing using copatterns. For a reference on copatterns,
   see https://agda.readthedocs.io/en/stable/language/copatterns.html.
-}

Σ-assoc' : {A : Set} {B : A → Set} {C : (x : A) → B x → Set}
        → Σ[ x ∈ A ] (Σ[ y ∈ B x ] (C x y))
          ≃
          Σ[ xy ∈ Σ[ x ∈ A ] (B x) ] (C (proj₁ xy) (proj₂ xy))

to Σ-assoc'      = λ z → (z .proj₁ , z .proj₂ .proj₁) , z .proj₂ .proj₂
from Σ-assoc'    = λ z → proj₁ (z .proj₁) , proj₂ (z .proj₁) , z .proj₂
from∘to Σ-assoc' = λ _ → refl
to∘from Σ-assoc' = λ _ → refl


----------------
-- Exercise 4 --
----------------


{-
   Prove that the `List` type former preserves isomorphisms.

   Hint: You might find it useful to use the `map` function on lists, together
   with the lemmas we imported from `Data.List.Properties`.
-}

list-eta : {A : Set} {x y : A} {xs ys : List A} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
list-eta refl refl = refl

≃-List : {A B : Set} → A ≃ B → List A ≃ List B
≃-List {A} {B} record { to = i ; from = j ; from∘to = p ; to∘from = q } =
  record
    { to = map i
    ; from = map j
    ; from∘to = from∘to-aux
    ; to∘from = to∘from-aux
    }
    where
      from∘to-aux : (xs : List A) → map j (map i xs) ≡ xs
      from∘to-aux [] = refl
      from∘to-aux (x ∷ xs) = list-eta (p x) (from∘to-aux xs)

      to∘from-aux : (ys : List B) → map i (map j ys) ≡ ys
      to∘from-aux [] = refl
      to∘from-aux (y ∷ ys) = list-eta (q y) (to∘from-aux ys)

≃-List' : {A B : Set} → A ≃ B → List A ≃ List B
≃-List' i .to               = map (to i)
≃-List' i .from             = map (from i)
≃-List' i .from∘to []       = refl
≃-List' i .from∘to (x ∷ xs) = list-eta (i .from∘to x) (≃-List' i .from∘to xs)
≃-List' i .to∘from []       = refl
≃-List' i .to∘from (y ∷ ys) = list-eta (i .to∘from y) (≃-List' i .to∘from ys)


----------------
-- Exercise 5 --
----------------


{-
   We now move on to decidable types. In particular, if we wish to search for
   elements of a list, we need to be able to decide the equality between any two
   elements.
-}

data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : (¬ A) → Dec A

record DecSet : Set₁ where
  field
    DSet   : Set
    test-≡ : (x y : DSet) → Dec (x ≡ y)

open DecSet

{-
   Given a type with decidable equality, prove that a list holding
   elements of this type is itself a type with decidable equality.
-}

DecList : (DS : DecSet) → Σ[ DS' ∈ DecSet ] (DSet DS' ≡ List (DSet DS))
DecList DS .proj₁ = record { DSet = DecList-DSet ; test-≡ = DecList-test-≡ }
   where
      DecList-DSet : Set
      DecList-DSet = List (DSet DS)

      DecList-test-≡ : (xs ys : List (DSet DS)) → Dec (xs ≡ ys)
      DecList-test-≡ [] [] = yes refl
      DecList-test-≡ [] (x ∷ ys) = no (λ ())
      DecList-test-≡ (x ∷ xs) [] = no (λ ())
      DecList-test-≡ (x ∷ xs) (y ∷ ys) with test-≡ DS x y
      ... | no ¬p = no λ { refl → ¬p refl}
      ... | yes refl with DecList-test-≡ xs ys
      ...               | no ¬q = no λ {refl → ¬q refl}
      ...               | yes refl = yes refl
DecList DS .proj₂ = refl
