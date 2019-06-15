module SizedList where

open import Size
open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Function

-- Guillaume def
data SList1 (A : Set) : Size -> Set where
  nil1 : ∀ {i} -> SList1 A (↑ i)
  cons1 : ∀ {i} ->  A -> SList1 A i -> SList1 A (↑ i)

select1 : ∀ {A i} -> (A -> Bool) -> SList1 A i -> SList1 A _
select1 p nil1 = nil1
select1 p (cons1 x l) with (p x)
... | false = select1 p l
... | true = cons1 x (select1 p l)

unchanged1 : ∀ {A i} -> (l : SList1 A i) -> select1 (const true) l ≡ l
unchanged1 nil1 =   {!!}  -- refl -- error : ∞ != i of type Size
unchanged1 (cons1 x l) rewrite (unchanged1 l)
  =  {!!} -- refl -- error : ∞ != i of type Size
  

-- Variation on Guillaume def
data SList2 (A : Set) : Size -> Set where
  nil2 : ∀ {i} ->  SList2 A i
  cons2 : ∀ {i} -> A -> SList2 A i -> SList2 A (↑ i)

select2 : ∀ {A i} -> (A -> Bool) -> SList2 A i -> SList2 A _
select2 p nil2 = nil2
select2 p (cons2 x l) with (p x)
... | false = select2 p l
... | true = cons2 x (select2 p l)

unchanged2 : ∀ {A i} -> (l : SList2 A i) -> select2 (const true) l ≡ l
unchanged2 nil2 = refl
unchanged2 (cons2 x l)  rewrite (unchanged2 l)
  =  {!!} -- refl -- error : ∞ != i of type Size

-- Andrew def
data SList3 (A : Set) (i : Size) : Set where
  nil3 : SList3 A i
  cons3 : ∀ {j : Size< i} -> A -> SList3 A j -> SList3 A i

append3 : ∀ {A k}{i j : Size< (↑ k)} -> SList3 A i -> SList3 A j -> SList3 A k
append3 nil3 l2 = l2
append3 (cons3 x l) l2 = cons3 x (append3 l l2) 

append-nil3 : ∀ {A i} -> (l : SList3 A i) -> append3 l nil3 ≡ l
append-nil3 nil3 = refl
append-nil3 (cons3 x l) rewrite (append-nil3 l)
   = {!!} -- refl -- error : ∞ != j of type Size
   
-- without any size (the witness case)

data List (A : Set) : Set where
  nil : List A
  cons : A -> List A -> List A

append : ∀ {A} -> List A -> List A  -> List A
append nil l2 = l2
append (cons x l) l2 = cons x (append l l2) 

append-nil : ∀ {A} -> (l : List A) -> append l nil ≡ l
append-nil nil = refl
append-nil (cons x l) rewrite (append-nil l)
   = refl

select : ∀ {A} -> (A -> Bool) -> List A -> List A
select p nil = nil
select p (cons x l) with (p x)
... | false = select p l
... | true = cons x (select p l)

unchanged : ∀ {A} -> (l : List A) -> select (const true) l ≡ l
unchanged nil = refl
unchanged (cons x l)  rewrite (unchanged l)
  = refl
   
