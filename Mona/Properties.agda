{-# OPTIONS --without-K #-}

-- Gathering the various generic definitions and properties whe shall use with Mona

open import Level


module Properties {l : Level} where

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product


-- variable l : Level

-- * Functor

Map : (F : Set l -> Set l) -> Set (suc l)
Map  F  =  ∀ {A B : Set l}  -> (A -> B) -> F A -> F B

module isFunctorMap where

  MapId :  ∀ {F : Set l -> Set l} -> (map : Map F) -> Set (suc l)
  MapId {F}  map = ∀ {A} -> (m : F A) -> (map {A} {A} id) m ≡ m

  MapCompose :  ∀ {F : Set l -> Set l} -> (map : Map F) -> Set (suc l)
  MapCompose {F} map = ∀ {A B C} {f : A -> B} {g : B -> C} ->
      (m : F A) -> map (g ∘ f) m ≡ (map g ∘ map f) m

-- * Monoid (uniformy defined)

Op : (G : Set l -> Set l) -> Set (suc l)
Op G = ∀ {A : Set l} -> G A -> G A -> G A

OpF : (FoG G : Set l -> Set l) -> Set (suc l)
OpF FoG G = ∀ {A : Set l} -> FoG A -> G A ->  FoG A
  -- with FoG some composition of F and G

Unit : (G : Set l -> Set l ) -> Set (suc l)
Unit G = ∀ {A : Set l} -> G A

module isMonoid where
  LeftUnit : ∀ {G} -> Op G -> Unit  G -> Set (suc l)
  LeftUnit {G} prod one = ∀ {A} -> (x : G A) -> prod one  x ≡ x

  RightUnit : ∀ {G} -> Op G -> Unit  G -> Set (suc l)
  RightUnit {G}  prod one = ∀ {A} -> (x : G A) -> prod x one ≡ x

  RightUnitF : ∀ {FoG G} -> OpF FoG G -> Unit  G -> Set (suc l)
  RightUnitF {FoG} {G}  prodF one = ∀ {A} -> (x : FoG A) -> prodF x one ≡ x

  Assoc : ∀ {G} -> Op G -> Set (suc l)
  Assoc {G} prod = ∀ {A} -> (x y z : G A) -> prod (prod x y) z ≡ prod x (prod y z)

  AssocF : ∀ {FoG G} -> OpF FoG G -> Op G -> Set (suc l)
  AssocF {FoG} {G} prodF prod = ∀ {A} -> (x : FoG A) -> (y z : G A)
        -> prodF (prodF x y) z ≡ prodF x (prod y z)



-- * Monad

Return : (Set l -> Set l) -> Set (suc l)
Return F = ∀ {A} -> A -> F A

Join : (Set l -> Set l)  -> Set (suc l)
Join F = ∀ {A} -> F (F A) ->  F A

Bind : (Set l -> Set l) -> Set (suc l)
Bind F = ∀ {A B} -> F A -> (A -> F B) -> F B

module isMonad where
  ReturnMap :  ∀ {F : Set l -> Set l} -> Map F -> Return F -> Set (suc l)
  ReturnMap map return = ∀ {A B}{f : A -> B} -> (x : A)
     -> return (f x) ≡ map f (return x)

  ReturnBind : ∀ {F : Set l -> Set l} -> Return F -> Bind F -> Set (suc l)
  ReturnBind {F} return bind
   = ∀ {A B} -> (x : A) -> (f : A -> F B) -> bind (return x) f ≡ f x

  BindReturn : ∀ {F : Set l -> Set l} -> Return F -> Bind F -> Set (suc l)
  BindReturn {F} return bind = ∀ {A} -> (m : F A) -> bind m return ≡ m

  BindAssoc : ∀ {F : Set l -> Set l} -> Bind F -> Set (suc l)
  BindAssoc {F} bind
    = ∀ {A B C} -> (m : F A) -> (f : A -> F B) -> (g : B -> F C)
       -> bind (bind m f) g ≡ bind m (λ x -> bind (f x) g)

  MapJoinBind  :  ∀ {F : Set l -> Set l} -> Map F -> Join F -> Bind F -> Set (suc l)
  MapJoinBind {F} map join bind
     = ∀ {A B} -> (m : F A) -> (f : A -> F B) -> bind m f ≡ join (map f m)
  
  BindJoin  :  ∀ {F : Set l -> Set l} -> Bind F -> Join F  -> Set (suc l)
  BindJoin {F} bind join = ∀ {A} -> (mm : F (F A)) ->  join mm ≡ bind mm id

  BindReturnMap  :  ∀ {F : Set l -> Set l} -> Bind F -> Return F -> Map F  -> Set (suc l)
  BindReturnMap {F} bind return map = ∀ {A B} -> (f : A -> B) -> (mm : F A)
        ->  map f mm ≡ bind mm (return  ∘ f)


  


