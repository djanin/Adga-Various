{-# OPTIONS --without-K #-}

-- Gathering the various generic definitions and properties whe shall use with Mona

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product


module Properties where

-- * Functor

Map : (F : Set -> Set) -> Set1
Map  F  =  ∀ {A B : Set}  -> (A -> B) -> F A -> F B

module isFunctorMap where

  MapId :  ∀ {F : Set -> Set} -> (map : Map F) -> Set1
  MapId {F}  map = ∀ {A} -> (m : F A) -> (map {A} {A} id) m ≡ m

  MapCompose :  ∀ {F : Set -> Set} -> (map : Map F) -> Set1
  MapCompose {F} map = ∀ {A B C} {f : A -> B} {g : B -> C} ->
      (m : F A) -> map (g ∘ f) m ≡ (map g ∘ map f) m

-- * Monoid (uniformy defined)

Op : (G : Set -> Set) -> Set1
Op G = ∀ {A : Set} -> G A -> G A -> G A

OpF : (FoG G : Set -> Set) -> Set1
OpF FoG G = ∀ {A : Set} -> FoG A -> G A ->  FoG A
  -- with FoG some composition of F and G

Unit : (G : Set -> Set ) -> Set1
Unit G = ∀ {A : Set} -> G A

module isMonoid where
  LeftUnit : ∀ {G} -> Op G -> Unit  G -> Set1
  LeftUnit {G} prod one = ∀ {A} -> (x : G A) -> prod one  x ≡ x

  RightUnit : ∀ {G} -> Op G -> Unit  G -> Set1
  RightUnit {G}  prod one = ∀ {A} -> (x : G A) -> prod x one ≡ x

  RightUnitF : ∀ {FoG G} -> OpF FoG G -> Unit  G -> Set1
  RightUnitF {FoG} {G}  prodF one = ∀ {A} -> (x : FoG A) -> prodF x one ≡ x

  Assoc : ∀ {G} -> Op G -> Set1
  Assoc {G} prod = ∀ {A} -> (x y z : G A) -> prod (prod x y) z ≡ prod x (prod y z)

  AssocF : ∀ {FoG G} -> OpF FoG G -> Op G -> Set1
  AssocF {FoG} {G} prodF prod = ∀ {A} -> (x : FoG A) -> (y z : G A)
        -> prodF (prodF x y) z ≡ prodF x (prod y z)



-- * Monad

Return : (Set -> Set) -> Set1
Return F = ∀ {A} -> A -> F A

Join : (Set -> Set)  -> Set1
Join F = ∀ {A} -> F (F A) ->  F A

Bind : (Set -> Set) -> Set1
Bind F = ∀ {A B} -> F A -> (A -> F B) -> F B

module isMonad where
  ReturnMap :  ∀ {F : Set -> Set} -> Map F -> Return F -> Set1
  ReturnMap map return = ∀ {A B}{f : A -> B} -> (x : A)
     -> return (f x) ≡ map f (return x)

  ReturnBind : ∀ {F : Set -> Set} -> Return F -> Bind F -> Set1
  ReturnBind {F} return bind
   = ∀ {A B} -> (x : A) -> (f : A -> F B) -> bind (return x) f ≡ f x

  BindReturn : ∀ {F : Set -> Set} -> Return F -> Bind F -> Set1
  BindReturn {F} return bind = ∀ {A} -> (m : F A) -> bind m return ≡ m

  BindAssoc : ∀ {F : Set -> Set} -> Bind F -> Set1
  BindAssoc {F} bind
    = ∀ {A B C} -> (m : F A) -> (f : A -> F B) -> (g : B -> F C)
       -> bind (bind m f) g ≡ bind m (λ x -> bind (f x) g)

  MapJoinBind  :  ∀ {F : Set -> Set} -> Map F -> Join F -> Bind F -> Set1
  MapJoinBind {F} map join bind
     = ∀ {A B} -> (m : F A) -> (f : A -> F B) -> bind m f ≡ join (map f m)
  
  BindJoin  :  ∀ {F : Set -> Set} -> Bind F -> Join F  -> Set1
  BindJoin {F} bind join = ∀ {A} -> (mm : F (F A)) ->  join mm ≡ bind mm id

  BindReturnMap  :  ∀ {F : Set -> Set} -> Bind F -> Return F -> Map F  -> Set1
  BindReturnMap {F} bind return map = ∀ {A B} -> (f : A -> B) -> (mm : F A)
        ->  map f mm ≡ bind mm (return  ∘ f)


  


