{-# OPTIONS --prop #-}

---------------------------------------------------------------------------
-- Week 6 exercises for the Logika v računalništvu course at UL FMF      --
-- Lecturer: Alex Simpson                                                --
-- Teaching Assistant: Luna Strah                                        --
--                                                                       --
-- Adapted from Danel Ahmans's exercises from 2022 available at:         --
-- https://github.com/danelahman/lograc-2022/blob/main/exercises/        --
--                                                                       --
-- Course website: https://ucilnica.fmf.uni-lj.si/course/view.php?id=252 --
---------------------------------------------------------------------------

module Ex6 where

----------------
-- Exercise 0 --
----------------

{-
   Begin by loading this Agda file in the editor of your choice (VS Code or Emacs, see README.md)
   using the `C-c C-l` command (to be read as pressing the `Ctrl` and `c` keys simultaneously,
   followed by pressing `Ctrl` and `l` keys simultaneously).

   If you have Agda set up correctly, then this should start the typechecking process on the given
   file. If the file loading and typechecking succeeds, the syntax should get colour-highlighted,
   and an additional buffer should appear and list the open goals (holes in Agda terminology) that
   need to be filled in this file:

   ?0 : Bool
   ?1 : ℕ
   ?2 : ℕ
   ...
   ?13 : length xs ≡ᴺ length (map f xs)
   ?14 : length xs ≤ length ys
   ?15 : xs ≤ᴸ ys
-}


----------------
-- Exercise 1 --
----------------

{-
   Recall the type of natural numbers from the lecture.
-}

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

{-
   Define a function that increments the given number by one.

   You can pattern-match on the function arguments by writing the name of the corresponding argument
   in the hole in the right-hand side of the definition, and then running the `C-c C-c` command with
   the cursor placed in the given hole.

   You can fill and complete a hole with what you have written in it by putting the cursor in the
   hole and then running the `C-c C-space` command. If you attempted to fill a hole with a term of
   incorrect type (say using something other than a natural number), Agda will report a typechecking
   error.
-}

incr : ℕ → ℕ
incr n = {!!}

{-
   Define a function that decrements a number by one. Give the definition using pattern-matching.
   Decrementing the number zero should return zero.
-}

decr : ℕ → ℕ
decr n = {!!}

{-
   Define a function that triples the value of a given number. Your definition should use both
   pattern-matching and recursion.
-}

triple : ℕ → ℕ
triple n = {!!}


----------------
-- Exercise 2 --
----------------

{-
   Recall the defintion of `+` from the lecture and/or exercise classes.
-}

_+_ : ℕ → ℕ → ℕ
zero    + n = n
(suc m) + n = suc (m + n)

{-# BUILTIN NATPLUS _+_ #-}

infixl 6  _+_

{-
   Define multiplication and exponentiation (`m^n`) using pattern-matching, recursion, and the
   operations on natural numbers defined above.
-}

_*_ : ℕ → ℕ → ℕ
m * n = {!!}
{-
   After finishing the task above uncomment the line below. If you made a mistake in the definition,
   Agda should give you an error once you reload.
-}
--{-# BUILTIN NATTIMES _*_ #-}

infixl 7  _*_

_^_ : ℕ → ℕ → ℕ
m ^ n = {!!}

infixl 8  _^_


----------------
-- Exercise 3 --
----------------

{-
   Another common inductive data structure you will often see in functional programming and in Agda
   is that of lists (holding elements of some type `A`), given by constructors for the empty list
   and for concatenating a new element to a given list.

   For example, the sequence of numbers 0, 1, 2 would be expressed in Agda as a list as the
   expression `0 ∷ 1 ∷ 2 ∷ []` of type `List ℕ`.
-}

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

{-# BUILTIN LIST List #-}
{-
   Define the `length` function that computes the length of a given list.
-}

length : {A : Set} → List A → ℕ
length xs = {!!}


----------------
-- Exercise 4 --
----------------

{-
   Define the `map` function on lists that applies a given function of type `A → B` to every element
   of a given list of type `List A` and returns a list of type `List B`. In other words, the
   application `map f (0 ∷ 1 ∷ 2 ∷ [])` should return `f 0 ∷ f 1 ∷ f 2 ∷ []`.
-}

map : {A B : Set} → (A → B) → List A → List B
map f xs = {!!}


----------------
-- Exercise 5 --
----------------

{-
   We can similarly define the type of vectors.
-}

data Vec (A : Set) : ℕ → Set where
  []ᵛ  : Vec A 0
  _∷ᵛ_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

infixr 5 _∷ᵛ_

{-
   Define the `length` function that computes the length of a given vector.
-}

lengthᵛ : {A : Set} {n : ℕ} → Vec A n → ℕ
lengthᵛ xs = {!!}


----------------
-- Exercise 6 --
----------------

{-
   Define the `map` function on vectors.
-}

mapᵛ : {A B : Set} → (A → B) → {n : ℕ} → Vec A n → Vec B n
mapᵛ f xs = {!!}


----------------
-- Exercise 6 --
----------------

{-
   There are several ways of defining relations on types. For example, lets define the ≤ relation on
   natural numbers.
-}

module WithProp where
  data _≤_ : ℕ → ℕ → Prop where
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

  infix 4 _≤_

module WithSet where
  data _≤_ : ℕ → ℕ → Set where
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

  infix 4 _≤_

module WithProp₂ where
  open WithProp

  {-
    However trying to define a Type-elimination principle for `≤` with `Prop` fails. You can attempt
    to finish the definition below, but since you are unable to pattern-match on `p`.
  -}
  module _ (P : (m n : ℕ) → Set)
    (pzn : (n : ℕ) → P zero n)
    (pss : (m n : ℕ) → P m n → P (suc m) (suc n)) where

    ≤-ind : (m n : ℕ) → m ≤ n → P m n
    ≤-ind zero    n       p = pzn n
    ≤-ind (suc m) (suc n) p = {!!}
    --≤-ind (suc m) (suc n) p = pss m n (≤-ind m n p)


module WithSet₂ where
  open WithSet

  module _ (P : (m n : ℕ) → Set)
    (pzn : (n : ℕ) → P zero n)
    (pss : (m n : ℕ) → P m n → P (suc m) (suc n)) where

    ≤-ind : (m n : ℕ) → m ≤ n → P m n
    ≤-ind m n z≤n = pzn n
    ≤-ind m n (s≤s p) = pss _ _ (≤-ind _ _ p)
    -- Here we must omit the arguments to `pss` and `≤-ind`, since they should be predecessors of
    -- `m` and n. Alternatively, we should pattern-match on `m` and `n` to extract their
    -- predecessors (we already know they are successors).


module WithPropButWithSetEliminationAsWell where

  data ⊥ᵖ : Prop where

  record ⊤ᵖ : Prop where
    constructor tt

  _≤_ : ℕ → ℕ → Prop
  zero  ≤ n     = ⊤ᵖ
  suc m ≤ zero  = ⊥ᵖ
  suc m ≤ suc n = m ≤ n

  infix 4 _≤_

  module _ {P : (m n : ℕ) → Set}
    (pzn : (n : ℕ) → P zero n)
    (pss : (m n : ℕ) → P m n → P (suc m) (suc n)) where

    ≤-ind : (m n : ℕ) → m ≤ n → P m n
    ≤-ind zero n p = pzn n
    ≤-ind (suc m) (suc n) p = pss m n (≤-ind m n p)

open WithPropButWithSetEliminationAsWell
open WithSet using () renaming (_≤_ to _≤ˢ_; z≤n to z≤ˢn; s≤s to s≤ˢs)

to-set : (m n : ℕ) → m ≤ n → m ≤ˢ n
to-set = ≤-ind (λ _ → z≤ˢn) λ _ _ → s≤ˢs

to-set' : (m n : ℕ) → m ≤ n → m ≤ˢ n
to-set' zero n p = z≤ˢn
to-set' (suc m) (suc n) p = s≤ˢs (to-set' m n p)

to-prop : (m n : ℕ) → m ≤ˢ n → m ≤ n
to-prop zero n p = tt
to-prop (suc m) (suc n) (s≤ˢs p) = to-prop m n p


----------------
-- Exercise 7 --
----------------

{-
   Show that the relation gives a preorder on ℕ.
-}

reflexive : (n : ℕ) → n ≤ n
reflexive n = {!!}

transitive : (m n k : ℕ) → m ≤ n → n ≤ k → m ≤ k
transitive n m k p q = {!!}


----------------
-- Exercise 8 --
----------------

{-
   To show that the relation is a partial order we need a notion of equality. We can define
   propositional equality as we did in the lectures.
-}

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_  #-}

anti-symmetric : (m n : ℕ) → m ≤ n → n ≤ m → m ≡ n
anti-symmetric zero zero p q = refl
anti-symmetric (suc m) (suc n) p q with anti-symmetric m n p q
... | refl = refl

anti-symmetricˢ : (m n : ℕ) → m ≤ˢ n → n ≤ˢ m → m ≡ n
anti-symmetricˢ m n z≤ˢn z≤ˢn = refl
anti-symmetricˢ m n (s≤ˢs p) (s≤ˢs q) with anti-symmetricˢ _ _ p q
... | refl = refl

------------------
-- Exercise 1 --
------------------

{-
   Recall the type of booleans from the lecture.
-}

data Bool : Set where
  true  : Bool
  false : Bool

{-
   Define the XOR operation on booleans by pattern-matching.

   Recall that you can pattern-match on the function arguments by
   writing the name of the corresponding argument in the hole in the
   right-hand side of the definition, and then running the `C-c C-c`
   command with the cursor placed in the given hole.

   Also recall that you can fill and complete a hole with what you
   have written in it by putting the cursor in the hole and then
   running the `C-c C-space` command. If you attempted to fill a
   hole with a term of incorrect type (say using a natural number
   instead of a boolean), Agda will report a typechecking error.
-}

_⊕_ : Bool → Bool → Bool
b ⊕ b' = {!!}

{-
   You can test whether your definition computes correctly by using
   the `C-c C-n` command, which uses Agda's normalisation engine to
   compute the normal form of a given expression. For example, using
   `C-c C-n` on `false ⊕ (true ⊕ false)` should return `true`.

   Feel free to use `C-c C-n` also with other functions on this
   exercise sheet to test whether your solutions compute correctly.
-}


----------------
-- Exercise 4 --
----------------

{-
   In addition to the unary representation of natural numbers
   given above and in the lecture (the ℕ type), one can represent
   natural numbers more compactly and more efficiently in binary
   format as bitstrings, defined as the following datatype Bin.

   For example, in Agda one represents the binary number 1010₂
   (which stands for the natural number 10) as `⟨⟩ I O I O`.

   You get the unicode symbol `⟨` by entering either `\<` or `\langle`,
   and the unicode symbol `⟩` by entering either `\>` or `\rangle`.
-}

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

infixl 20 _O
infixl 20 _I

{-
   Define the increment function on such binary numbers, e.g.,
   such that you have `b-incr (⟨⟩ I O I I) ≡ ⟨⟩ I I O O`.
-}

b-incr : Bin → Bin
b-incr b = {!!}


----------------
-- Exercise 5 --
----------------

{-
   Define functions `to` and `from` that translate unary numbers
   to binary numbers and vice versa. If needed for the solution,
   don't be afraid of defining and using new auxiliary functions
   (either using a `where` clause or by defining these auxiliary
   functions at the top level before the function where you
   want to use them).
-}

to : ℕ → Bin
to n = {!!}

from : Bin → ℕ
from b = {!!}


----------------
-- Exercise 6 --
----------------

{-
   Recall the "is even" predicate for unary numbers.
-}

data Even : ℕ → Set where
  even-z : Even zero
  even-ss : {n : ℕ} → Even n → Even (suc (suc n))

{-
   Define an analogous "is even" predicate for binary numbers.
-}

data Even₂ : Bin → Set where
  {- EXERCISE: add the constructors for this inductive predicate here -}


----------------
-- Exercise 7 --
----------------

{-
   Prove that the `to` function translates evens to evens. Again,
   if needed, do not be afraid to define auxiliary functions/proofs.
-}

to-even : {n : ℕ} → Even n → Even₂ (to n)
to-even p = {!!}


----------------
-- Exercise 8 --
----------------

{-
   Observe that for the simplicity and uniformity of its definition,
   the type Bin has redundant elements---in your above solutions, you
   likely treated both `⟨⟩` and `⟨⟩ O` both as the unary number 0.

   Define a unary inductive predicate NonEmptyBin to classify those
   binary numbers that are non-empty in the sense that `⟨⟩` is not a
   non-empty binary number on its own---it can only terminate a
   sequence of Os and Is from the left. In other words, the type
   `NonEmptyBin (⟨⟩ I O I I)` should be inhabited while the type
   `NonEmptyBin ⟨⟩` should not be inhabited.
-}

data NonEmptyBin : Bin → Set where
  {- EXERCISE: add the constructors for this inductive predicate here -}

{-
   To verify that `NonEmptyBin ⟨⟩` is indeed not inhabited as intended,
   show that you can define a function from it to Agda's empty type
   (an inductive type with no constructors, hence with no inhabitants).
-}

data ⊥ : Set where

⟨⟩-empty : NonEmptyBin ⟨⟩ → ⊥
⟨⟩-empty p = {!!}


----------------
-- Exercise 9 --
----------------

{-
   Using the non-empty binary numbers predicate, rewrite the `from`
   function so that it takes an additional proof argument that
   witnesses that the given binary number argument is non-empty.

   Due to this additional proof argument, your solution will not
   need a case for the binary number argument being `⟨⟩` any more.
-}

from-ne : (b : Bin) → NonEmptyBin b → ℕ
from-ne b p = {!!}


-----------------
-- Exercise 12 --
-----------------

{-
   Recall the (observational) equality relation for unary numbers.
-}

infix 4 _≡ᴺ_

data _≡ᴺ_ : ℕ → ℕ → Set where
  z≡ᴺz : zero ≡ᴺ zero
  s≡ᴺs : {m n : ℕ} → m ≡ᴺ n → suc m ≡ᴺ suc n

{-
   Prove that the `map` function preserves the length of the given list.
-}

map-≡ᴺ : {A B : Set} {f : A → B} → (xs : List A) → length xs ≡ᴺ length (map f xs)
map-≡ᴺ xs = {!!}


-----------------
-- Exercise 13 --
-----------------

{-
   Recall the "less than or equal" relation on unary numbers.
-}


{-
   Define an analogous inductive binary relation `≤ᴸ` for lists
   based on their lengths,  e.g., `[]` should be less than or
   equal (using `≤ᴸ`) to the lists `[]` and `[ 42 ]`.
-}

data _≤ᴸ_ {A : Set} : List A → List A → Set where
  {- EXERCISE: add the constructors for this inductive relation here -}

infix 4 _≤ᴸ_


-----------------
-- Exercise 14 --
-----------------

{-
   Prove that the lengths of two lists related by `≤ᴸ` are related
   by the `≤` relation, and vice versa.
-}

-- length-≤ᴸ-≦ : {A : Set} {xs ys : List A} → xs ≤ᴸ ys → length xs ≤ length ys
-- length-≤ᴸ-≦ p = {!!}

-- length-≤-≦ᴸ : {A : Set} (xs ys : List A) → length xs ≤ length ys → xs ≤ᴸ ys
-- length-≤-≦ᴸ xs ys p = {!!}


-----------------
-- Exercise 14 --
-----------------

{-
   If you have solved all the above exercises, then as extra, more
   challening problems, you can try to equip the binary numbers with
   operations and relations we have defined for the unary numbers:
   - addition
   - multiplication
   - (observational) equality
   - "less than or equal" order
   - show that `from` takes even numbers to even numbers
-}
