{-# OPTIONS --prop --rewriting #-}
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

module Ex8 where

open import Data.Empty           using (⊥; ⊥-elim)
open import Data.Fin             using (Fin; zero; suc)
open import Data.List            using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (map-id; map-compose)
open import Data.Maybe           using (Maybe; nothing; just)
--open import Data.Nat             using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _<_)
open import Data.Nat             using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties  using (+-identityˡ; +-identityʳ; +-suc; +-comm)
open import Data.Product         using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.Vec             using (Vec; []; _∷_)

open import Function             using (id; _∘_)

open import Relation.Nullary     using (¬_)

import Relation.Binary.PropositionalEquality as Eq
open Eq                          using (_≡_; refl; sym; trans; cong; subst; _≢_)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

data ⊥ᵖ : Prop where

record ⊤ᵖ : Prop where
  constructor tt

_≤_ : ℕ → ℕ → Prop
zero  ≤ n     = ⊤ᵖ
suc m ≤ zero  = ⊥ᵖ
suc m ≤ suc n = m ≤ n

infix 4 _≤_

_<_ : ℕ → ℕ → Prop
n < m = suc n ≤ m

_>_ : ℕ → ℕ → Prop
n > m = m < n

infix 4 _<_
infix 4 _>_

----------------
-- Exercise 1 --
----------------

{-
   Here's the safe lookup function for lists (in terms of the `<` relation).
-}

safe-list-lookup : {A : Set} → (xs : List A) → (i : ℕ) → i < length xs → A
safe-list-lookup (x ∷ xs) zero    _ = x
safe-list-lookup (x ∷ xs) (suc i) p = safe-list-lookup xs i p

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
   ≡⟨ {!!} ⟩
     y ∷ xs
   ≡⟨ {!!} ⟩
     y ∷ ys
   ∎

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
vec-list-Σ xs = {!!}


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

Σ-assoc = {!!}

{-
   Second, prove the same thing using copatterns. For a reference on copatterns,
   see https://agda.readthedocs.io/en/stable/language/copatterns.html.
-}

Σ-assoc' : {A : Set} {B : A → Set} {C : (x : A) → B x → Set}
        → Σ[ x ∈ A ] (Σ[ y ∈ B x ] (C x y))
          ≃
          Σ[ xy ∈ Σ[ x ∈ A ] (B x) ] (C (proj₁ xy) (proj₂ xy))

Σ-assoc' = {!!}



----------------
-- Exercise 4 --
----------------


{-
   Prove that the `List` type former preserves isomorphisms.

   Hint: You might find it useful to use the `map` function on lists, together
   with the lemmas we imported from `Data.List.Properties`.
-}

≃-List : {A B : Set} → A ≃ B → List A ≃ List B
≃-List = {!!}




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
      DecList-test-≡ = {!!}
DecList DS .proj₂ = refl




----------------
-- Exercise 6 --
----------------

{-
   In various algorithms we will wish to keep track of already processed values,
   but would rather not keep duplicates in a list. We can do this with a
   modified `cons` operation, that will check for duplicates.
-}
module NoDupList where
  add : {DS : DecSet} → List (DSet DS) → DSet DS → List (DSet DS)
  add [] x' = x' ∷ []
  add {DS} (x ∷ xs) x' with (test-≡ DS) x x'
  ... | yes refl = x' ∷ xs
  ... | no  p    = x ∷ add {DS} xs x'

  {-
     Below we are going to make this intuitive correctness property of `add`
     formal by proving it in Agda.
  -}

  {-
     When thinking about how to specify that a given list has no duplicate
     elements, one likely first comes up with the `NoDup'` predicate below.
  -}

  safe-lookup : {A : Set} → (xs : List A) → Fin (length xs) → A
  safe-lookup (x ∷ xs) zero    = x
  safe-lookup (x ∷ xs) (suc n) = safe-lookup xs n

  NoDup' : {A : Set} → List A → Set
  NoDup' xs = (i j : Fin (length xs)) → i ≢ j → safe-lookup xs i ≢ safe-lookup xs j

  {-
     While this is a mathematically and logically natural statement (any distinct
     pair of indices holds distinct values), it is not the best definition for
     proving theorems about it in type theory. Instead of characterising a
     negative statement (e.g., no duplicates) using a combination of function
     types/implications and negations, it is generally better if negative
     statements are also defined more "structurally"---as inductively defined
     predicates that then follow the structure of the type they are defined over
     (e.g., `List A`).

     (You can of course also try to prove `add-nodup` using `NoDup'`.)

     (As a bonus exercise, you can also try to separately prove that the `NoDup`
     and `NoDup'` predicates are logically equivalent.)
  -}

  {-
     So, instead, give below an inductive definition to the `NoDup` predicate.

     Hint: You might find the `∈` relation on lists defined below useful.
  -}

  infix 3 _∈_

  data _∈_ {A : Set} : A → List A → Set where
    ∈-here  : {x : A} → {xs : List A} → x ∈ (x ∷ xs)
    ∈-there : {x y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

  data NoDup {A : Set} : List A → Set where
    {- EXERCISE: replace this comment with constructors for `NoDup` -}

  {-
     Next, prove some sanity-checks about the correctness of `NoDup`.
  -}

  nodup-test₁ : NoDup {ℕ} []
  nodup-test₁ = {!!}

  nodup-test₂ : NoDup (4 ∷ 2 ∷ [])
  nodup-test₂ = {!!}

  nodup-test₃ : ¬ (NoDup (4 ∷ 2 ∷ 4 ∷ []))
  nodup-test₃ = {!!}

  {-
     Finally, prove that `add` preserves the no-duplicates property.

     Hint: You might find it useful to prove an auxiliary lemma, showing that
     under certain conditions, if `x` is in `add xs x'`, then `x` was actually
     already present in `xs` (When would this be the case?).
  -}

  add-nodup : {DS : DecSet} → (xs : List (DSet DS)) → (x : DSet DS)
            → NoDup {DSet DS} xs
            → NoDup {DSet DS} (add {DS} xs x)
  add-nodup xs x' p = {!!}


----------------
-- Exercise 7 --
----------------

{-
   We have memberhood, but now we wish to also make assignments.
-}

module AssocList (K : DecSet) (V : Set) where

  AssocList : Set
  AssocList = List (DSet K × V)

  _∈_ : DSet K → AssocList → Set
  k ∈ kvs = k NoDupList.∈ (map proj₁ kvs)

  lookup : {k : DSet K} {kvs : AssocList} → k ∈ kvs → V
  lookup {kvs = []} ()
  lookup {kvs = (_ , v) ∷ _}    NoDupList.∈-here     = v
  lookup {kvs = (k , v) ∷ kvs} (NoDupList.∈-there p) = lookup p

  _∈?_ : (k : DSet K) → (kvs : AssocList) → Dec (k ∈ kvs)
  k ∈? [] = no λ ()
  k ∈? ((k' , _) ∷ kvs) with K .test-≡ k k'
  ... | yes refl = yes NoDupList.∈-here
  ... | no p with k ∈? kvs
  ...           | yes q = yes (NoDupList.∈-there q)
  ...           | no q = no (λ { NoDupList.∈-here → p refl ; (NoDupList.∈-there r) → q r})

  _‼_ : (kvs : AssocList) → (k : DSet K) → Maybe V
  kvs ‼ k with k ∈? kvs
  ... | yes p = just (lookup p)
  ... | no  _ = nothing

  _[_]≔_ : AssocList → DSet K → V → AssocList
  kvs [ k ]≔ v with k ∈? kvs
  ... | yes _ = kvs
  ... | no  _ = (k , v) ∷ kvs




{-
   Lets define a common interface we will use for the project.
-}

module Assoc (K : DecSet) (V : Set) where

  Assoc : Set
  Assoc = {!!}

  _∈_ : DSet K → Assoc → Set
  k ∈ kvs = {!!}

  lookup : {k : DSet K} {kvs : Assoc} → k ∈ kvs → V
  lookup p = {!!}

  _∈?_ : (k : DSet K) → (kvs : Assoc) → Dec (k ∈ kvs)
  k ∈? kvs = {!!}

  _‼_ : (kvs : Assoc) → (k : DSet K) → Maybe V
  kvs ‼ k = {!!}

  _[_]≔_ : Assoc → DSet K → V → Assoc
  kvs [ k ]≔ v = {!!}


𝒩 : DecSet
𝒩 .DSet = ℕ
𝒩 .test-≡ zero zero = yes refl
𝒩 .test-≡ zero (suc n) = no λ ()
𝒩 .test-≡ (suc m) zero = no λ ()
𝒩 .test-≡ (suc m) (suc n) with 𝒩 .test-≡ m n
... | yes refl = yes refl
... | no m≢n = no (λ {refl → m≢n refl})

open import Data.Bool using (Bool; true; false; not; _xor_; if_then_else_; _∧_)
open import Data.Bool.ListAction using (and; or)
open Assoc 𝒩 Bool

Assignment = Assoc
Literal = ℕ × Bool
Disjunct = List Literal
Conjunct = List Disjunct

eval : Conjunct → Assignment → Maybe Bool
eval φ assn = {!!}

-------------------------------------------------------------------
-- Bonus exercise on logical equivalence of `NoDup` and `NoDup'` --
-------------------------------------------------------------------

module _ where
  {-
     `NoDup` implies `NoDup'`
  -}

  open NoDupList
  nodup-nodup' : {A : Set} → (xs : List A) → NoDup xs → NoDup' xs
  nodup-nodup' = {!!}

  {-
     `NoDup'` implies `NoDup`
  -}

  nodup'-nodup : {A : Set} → (xs : List A) → NoDup' xs → NoDup xs
  nodup'-nodup = {!!}
