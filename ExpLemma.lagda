\begin{code}
module ExpLemma where
open import Data.Nat renaming (ℕ to Nat; zero to Z; suc to S)
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; refl; cong)
open PropEq.≡-Reasoning
\end{code}

The module |PropEq| defines convenient operators for reasoning with
equivalence relations, including the special case of propositional
equality (in the submodule |≡-Reasoning|).

This file is intended as an illustration of the style of equational
reasoning that Agda (and Idris) supports.

\begin{code}
postulate
  Real : Set
  one  : Real
  _*R_ : Real -> Real -> Real
  unitMult   : (y : Real) -> one *R y ≡ y
  assocMult  : (x : Real) -> (y : Real) ->  (z : Real) ->  (x *R y) *R z ≡ x *R (y *R z)

infixl 9 _*R_

infixr 10 _^_
_^_ : Real -> Nat -> Real
x ^ Z      = one
x ^ (S n)  = x *R (x ^ n)
\end{code}

Equality and equational reasoning

Let's prove a lemma about exponentiation by induction over the first
|Nat| argument.
%
Then the three definitions we need to implement have the following types:

\begin{code}
expLemma :  (x : Real) -> (m : Nat) -> (n : Nat) -> (x ^ m *R x ^ n ≡ x ^ (m + n))
baseCase :  (x : Real) -> (n : Nat) -> (x ^ Z  *R  x ^ n ≡ x ^ (Z + n))
stepCase :  (x : Real) -> (m : Nat) -> (n : Nat) ->
            (ih :  x ^ m      *R  x ^ n ≡ x ^ (m + n))      ->
            (      x ^ (S m)  *R  x ^ n ≡ x ^ ((S m) + n))
\end{code}

The main lemma just uses the base case for zero and the step case for successor.
%
Note that the last argument to the step case is the induction
hypothesis: a recursive call to |expLemma|.

\begin{code}
expLemma x Z      n = baseCase x n
expLemma x (S m)  n = stepCase x m n (expLemma x m n)

baseCase x n =
  begin
     x ^ Z  *R  x ^ n
  ≡⟨  refl ⟩                        -- By definition of |_^_|
     one *R x ^ n
  ≡⟨ unitMult (x ^ n) ⟩             -- Use |one *R y = y| for |y = x ^ n|
       x ^ n
  ≡⟨ refl ⟩                         -- By definition of |_+_|
     x ^ (Z + n)
  ∎
\end{code}

\begin{code}
stepCase x m n ih =
  begin
     x ^ (S m) *R x ^ n
  ≡⟨ refl ⟩                         -- By definition of |_^_|
     (x *R x ^ m) *R x ^ n
  ≡⟨ assocMult x (x ^ m) (x ^ n) ⟩  -- Associativity of multiplication
     x *R (x ^ m  *R  x ^ n)
  ≡⟨ cong (_*R_ x) ih ⟩             -- Use the induction hypothesis |expLemma x m n|
     x *R x ^ (m + n)
  ≡⟨ refl ⟩                         -- By definition of |(^)| (backwards)
     x ^ (S (m + n))
  ≡⟨ refl ⟩                         -- By definition of |(+)|
     x ^ (S m + n)
  ∎
\end{code}
