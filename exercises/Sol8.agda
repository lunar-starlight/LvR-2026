{-# OPTIONS --prop #-}
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
open import Data.List.Properties using (map-id; map-∘)
open import Data.Maybe           using (Maybe; nothing; just)
open import Data.Product         using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.Vec             using (Vec; []; _∷_)

open import Function             using (id; _∘_)

open import Relation.Nullary     using (¬_)

import Relation.Binary.PropositionalEquality as Eq
open Eq                          using (_≡_; refl; sym; trans; cong; subst; _≢_)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

--open import Data.Nat             using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _<_)

{-
   `Prop`-based inequalities. You can instead use the standard library
   inequalities, by deleting the code below and uncommenting the `import
   Data.Nat` above. You might need to change some code below though.
-}
open import Data.Nat             using (ℕ; zero; suc; _+_)

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
   ≡⟨ cong (_∷ xs) (g 0 _ _) ⟩
     y ∷ xs
   ≡⟨ cong (y ∷_) (list-ext (suc-inj h) λ i p q → g (suc i) p q) ⟩
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
  { to      = λ z → (z .proj₁ , z .proj₂ .proj₁) , z .proj₂ .proj₂
  ; from    = λ z → proj₁ (z .proj₁) , proj₂ (z .proj₁) , z .proj₂
  ; from∘to = λ _ → refl
  ; to∘from = λ _ → refl
  }

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

≃-List'' : {A B : Set} → A ≃ B → List A ≃ List B
≃-List'' i .to        = map (to i)
≃-List'' i .from      = map (from i)
≃-List'' i .from∘to xs =
  begin
    map (from i) (map (to i) xs)
  ≡⟨ sym (map-∘ xs) ⟩
    map (from i ∘ to i) xs
  ≡⟨ cong (λ t → map t xs) (fun-ext (i .from∘to)) ⟩
    map id xs
  ≡⟨ map-id xs ⟩
    xs
  ∎
≃-List'' i .to∘from ys =
  begin
    map (to i) (map (from i) ys)
  ≡⟨ sym (map-∘ ys) ⟩
    map (to i ∘ from i) ys
  ≡⟨ cong (λ t → map t ys) (fun-ext (i .to∘from)) ⟩
    map id ys
  ≡⟨ map-id ys ⟩
    ys
  ∎


----------------
-- Exercise 5 --
----------------

{-
   We now move on to decidable types. In particular, if we wish to search for
   elements of a list, we need to be able to decide the equality between any two
   elements.
-}

{-
   The type `Dec A` says "we either have a term of type `A` or we have a proof
   that `A` is empty".
-}

data Dec (A : Set) : Set where
  yes :    A  → Dec A
  no  : (¬ A) → Dec A

{-
   Here `Set₁` has something to do with universe levels, which we likely will
   not cover in this course. You can think of it as "the type of classes", but
   it is safe to ignore.
-}

record DecType : Set₁ where
  field
    carr   : Set
    test-≡ : (x y : carr) → Dec (x ≡ y)

{-
   The type `DecType` is the type of "decidable types". It is a record type and
   it's elements have two fields; `carr` is the underlying type and `test-≡` is
   the "decidability predicate", deciding the equality between any two elements.

   In general not every type is decidable. Consider the type of infinite
   non-descending sequences of booleans. Then you can not write a program that
   decides whether a sequence is all zeroes, or if at some point it switches to
   a one. Consider what such a program will do. I can keep giving you zeroes as
   values of the sequence until at some finite time the program decides that the
   sequence either is or is not all zeroes. In either case from that point on I
   can decide that the sequence I had in mind is _not_ the sequence the program
   guessed. Since programs are deterministic and terminating, I can always
   construct a sequence, for which the program decides incorrectly. Thus, the
   type of infinite non-descending sequences of booleans is not decidable.
-}

open DecType

{-
   Given a type with decidable equality, prove that a list holding
   elements of this type is itself a type with decidable equality.
-}

DecList : (DS : DecType) → Σ[ DS' ∈ DecType ] (carr DS' ≡ List (carr DS))
DecList DS .proj₁ = record { carr = DecList-carr ; test-≡ = DecList-test-≡ }
   where
      DecList-carr : Set
      DecList-carr = List (carr DS)

      DecList-test-≡ : (xs ys : List (carr DS)) → Dec (xs ≡ ys)
      DecList-test-≡ [] [] = yes refl
      DecList-test-≡ [] (x ∷ ys) = no (λ ())
      DecList-test-≡ (x ∷ xs) [] = no (λ ())
      DecList-test-≡ (x ∷ xs) (y ∷ ys) with test-≡ DS x y
      ... | no ¬p = no λ { refl → ¬p refl}
      ... | yes refl with DecList-test-≡ xs ys
      ...               | no ¬q = no λ {refl → ¬q refl}
      ...               | yes refl = yes refl
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
  add : ⦃ DS : DecType ⦄ → List (carr DS) → carr DS → List (carr DS)
  add [] x' = x' ∷ []
  add ⦃ DS ⦄ (x ∷ xs) x' with (test-≡ DS) x x'
  ...                       | yes refl = x ∷ xs
  ...                       | no  p    = x ∷ add xs x'

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

  infix 4 _∈_

  data _∈_ {A : Set} : A → List A → Set where
    ∈-here  : {x : A} → {xs : List A} → x ∈ (x ∷ xs)
    ∈-there : {x y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

  data NoDup {A : Set} : List A → Set where
    []-nodup : NoDup []
    ∷-nodup : {x : A} {xs : List A} → NoDup xs → ¬ (x ∈ xs) → NoDup (x ∷ xs)

  {-
     Next, prove some sanity-checks about the correctness of `NoDup`.
  -}

  nodup-test₁ : NoDup {ℕ} []
  nodup-test₁ = []-nodup

  nodup-test₂ : NoDup (4 ∷ 2 ∷ [])
  nodup-test₂ = ∷-nodup (∷-nodup []-nodup (λ ())) (λ {(∈-there ())})

  nodup-test₃ : ¬ (NoDup (4 ∷ 2 ∷ 4 ∷ []))
  nodup-test₃ = λ { (∷-nodup p q) → q (∈-there ∈-here)}

  {-
     Finally, prove that `add` preserves the no-duplicates property.

     Hint: You might find it useful to prove an auxiliary lemma, showing that
     under certain conditions, if `x` is in `add xs x'`, then `x` was actually
     already present in `xs` (When would this be the case?).
  -}

  add-nodup : ⦃ DS : DecType ⦄ → (xs : List (carr DS)) → (y : carr DS)
            → NoDup xs
            → NoDup (add xs y)
  add-nodup [] y p = ∷-nodup p (λ ())
  add-nodup ⦃ DS ⦄ (x ∷ xs) y (∷-nodup p q) with DS .test-≡ x y
  ... | yes refl = ∷-nodup p q
  ... | no x≢y = ∷-nodup (add-nodup xs y p) (∈-add x≢y q)
    where
      ∈-add : {x y : carr DS} {xs : List (carr DS)} → x ≢ y → ¬ x ∈ xs → ¬ x ∈ add xs y
      ∈-add {_} {_} {[]} p q ∈-here = p refl
      ∈-add {_} {y} {x ∷ _} _ q r        with DS .test-≡ x y
      ...                                   | yes refl = q r
      ∈-add {_} {_} {_ ∷ _} _ q ∈-here      | no x≢y = q ∈-here
      ∈-add {_} {_} {_ ∷ _} p q (∈-there r) | no x≢y = ∈-add p (q ∘ ∈-there) r


----------------
-- Exercise 7 --
----------------

{-
   We have memberhood, but now we wish to also make assignments. Fill the below
   holes using solutions of previous exercises.

   Note: You will need to do some further work to implement some of these.
-}

module AssocList (K : DecType) (V : Set) where

  Assoc : Set
  Assoc = List (carr K × V)

  {- Elementhood relation -}
  _∈_ : carr K → Assoc → Set
  k ∈ kvs = k NoDupList.∈ (map proj₁ kvs)

  {- Safe lookup -}
  lookup : {k : carr K} {kvs : Assoc} → k ∈ kvs → V
  lookup {kvs = []} ()
  lookup {kvs = (_ , v) ∷ _}    NoDupList.∈-here     = v
  lookup {kvs = (k , v) ∷ kvs} (NoDupList.∈-there p) = lookup p

  {- The decidability of the elementhood relation -}
  _∈?_ : (k : carr K) → (kvs : Assoc) → Dec (k ∈ kvs)
  k ∈? [] = no λ ()
  k ∈? ((k' , _) ∷ kvs) with K .test-≡ k k'
  ... | yes refl = yes NoDupList.∈-here
  ... | no p with k ∈? kvs
  ...           | yes q = yes (NoDupList.∈-there q)
  ...           | no q = no (λ { NoDupList.∈-here → p refl ; (NoDupList.∈-there r) → q r})

  {- Lookup returning a maybe -}
  _‼_ : (kvs : Assoc) → (k : carr K) → Maybe V
  kvs ‼ k with k ∈? kvs
  ... | yes p = just (lookup p)
  ... | no  _ = nothing

  {-
     Update value

     Note: Here if `k` is not in `kvs` we append it to the front, otherwise we
     step into `kvs` and replace the odl value with the new value.
  -}
  _[_]≔_ : Assoc → carr K → V → Assoc
  kvs [ k ]≔ v with k ∈? kvs
  ... | yes _ = kvs
  ... | no  _ = (k , v) ∷ kvs


{-
   This is a common interface we will use for the project. You can define an
   alternative implementation here. A more involved implementation will be
   weighed higher in grading.

   Note: You might not need all of the below functions, and you might need more.
   This is just a first approximation of basic functionality we want from a
   lookup table-type structure: checking elementhood, looking up values, and
   updating the structure.
-}

module Assoc (K : DecType) (V : Set) where

  Assoc : Set
  Assoc = {!!}

  _∈_ : carr K → Assoc → Set
  k ∈ kvs = {!!}

  lookup : {k : carr K} {kvs : Assoc} → k ∈ kvs → V
  lookup p = {!!}

  _∈?_ : (k : carr K) → (kvs : Assoc) → Dec (k ∈ kvs)
  k ∈? kvs = {!!}

  _‼_ : (kvs : Assoc) → (k : carr K) → Maybe V
  kvs ‼ k = {!!}

  _[_]≔_ : Assoc → carr K → V → Assoc
  kvs [ k ]≔ v = {!!}


----------------
-- Exercise 8 --
----------------

{-
   We can now do some rudamentary work with CNF formulae.

   Recall that a formula is in CNF when it is a conjunction of disjunctions of
   literals, where literals are either variables or negations of variables.

   We will replresent arbitrary conjunctions and disjunctions simply with lists.
   Literals will be represented by a pair of a natural number (representing the
   index of the variable) and a boolean value, indicating whether the variable
   is negated.

   For example, the pair `(7 , false)` will represent the literal `¬x₇` (you can
   of course also choose to represent this literal by `(7 , true)`. There is no
   correct choice here, so you are free to chose either).

   Next week we will define a more structured (and Agda-like) definition of a
   formula, thereby avoiding the above connundrum.
-}

module _ where
  𝒩 : DecType
  𝒩 .carr = ℕ
  𝒩 .test-≡ zero zero = yes refl
  𝒩 .test-≡ zero (suc n) = no λ ()
  𝒩 .test-≡ (suc m) zero = no λ ()
  𝒩 .test-≡ (suc m) (suc n) with 𝒩 .test-≡ m n
  ... | yes refl = yes refl
  ... | no m≢n = no (λ {refl → m≢n refl})

  open import Data.Bool using (Bool; true; false; not; _xor_; if_then_else_; _∧_)
  open import Data.Bool.ListAction using (and; or)
  open AssocList 𝒩 Bool

  Assignment = Assoc
  Literal = ℕ × Bool
  Disjunct = List Literal
  Conjunct = List Disjunct

  {-
     Define an evaluation function for CNF formulae. It should return a value when
     all of the variables appearing in the formula are present in the given
     assignment, and return `nothing` otherwise.

     Note: If this means anything to you it might help: Maybe is a monad and the
     standard library defines the usual things that come with that somewhere in
     `Data.Maybe`. If you want to use those you should try to find them either in
     the local files or on the git repo at
     https://github.com/agda/agda-stdlib/blob/master/src/.
  -}

  _iff_ : Bool → Bool → Bool
  x iff y = not (x xor y)

  eval-disjunct : Disjunct → Assignment → Maybe Bool
  eval-disjunct [] assn = just false
  eval-disjunct ((k , v) ∷ D) assn with eval-disjunct D assn
  ... | nothing = nothing
  ... | just b with k ∈? assn
  ...             | no _  = nothing
  ...             | yes p = just ((lookup p iff v) ∧ b)

  eval : Conjunct → Assignment → Maybe Bool
  eval [] assn = just true
  eval (D ∷ C) assn with eval C assn
  ... | nothing = nothing
  ... | just b with eval-disjunct D assn
  ...             | nothing = nothing
  ...             | just b' = just (b' ∧ b)

-------------------------------------------------------------------
-- Bonus exercise on logical equivalence of `NoDup` and `NoDup'` --
-------------------------------------------------------------------

module _ where
  {-
     `NoDup` implies `NoDup'`
  -}

  open NoDupList

  ∈-to-≡safe-lookup : {A : Set} {x : A} {xs : List A} → x ∈ xs → Σ[ i ∈ Fin (length xs) ] x ≡ safe-lookup xs i
  ∈-to-≡safe-lookup {xs = []} ()
  ∈-to-≡safe-lookup {xs = _ ∷ _} ∈-here = zero , refl
  ∈-to-≡safe-lookup {xs = _ ∷ _} (∈-there p) with ∈-to-≡safe-lookup p
  ... | (i , q) = suc i , q
  ≡safe-lookup-to-∈ : {A : Set} {x : A} {xs : List A} → Σ[ i ∈ Fin (length xs) ] x ≡ safe-lookup xs i → x ∈ xs
  ≡safe-lookup-to-∈ {xs = []} (() , p)
  ≡safe-lookup-to-∈ {xs = x ∷ xs} (zero , refl) = ∈-here
  ≡safe-lookup-to-∈ {xs = x ∷ xs} (suc i , p) = ∈-there (≡safe-lookup-to-∈ (i , p))

  nodup-nodup' : {A : Set} → (xs : List A) → NoDup xs → NoDup' xs
  nodup-nodup' [] []-nodup = λ ()
  nodup-nodup' (x ∷ xs) (∷-nodup p q) zero zero r s = r refl
  nodup-nodup' (x ∷ xs) (∷-nodup p q) zero (suc j) r s = q (≡safe-lookup-to-∈ (j , s))
  nodup-nodup' (x ∷ xs) (∷-nodup p q) (suc i) zero r s = q (≡safe-lookup-to-∈ (i , sym s))
  nodup-nodup' (x ∷ xs) (∷-nodup p q) (suc i) (suc j) r s with nodup-nodup' xs p
  ...                                                        | v = v i j (λ { refl → r refl}) s

  {-
     `NoDup'` implies `NoDup`
  -}

  nodup'-nodup : {A : Set} → (xs : List A) → NoDup' xs → NoDup xs
  nodup'-nodup [] p = []-nodup
  nodup'-nodup {A} (x ∷ xs) p = ∷-nodup I (II p)
    where
      I : NoDup xs
      I = nodup'-nodup xs λ i j r s → p (suc i) (suc j) (λ {refl → r refl}) s

      II : {x : A} → {xs : List A} → NoDup' (x ∷ xs) → ¬ x ∈ xs
      II p q with ∈-to-≡safe-lookup q
      ...       | i , refl = p zero (suc i) (λ ()) refl
