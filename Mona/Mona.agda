{-# OPTIONS --without-K #-}

-- Playing around the ideas, concepts an techniques gathered and
-- pleasantly presented in the functional pearl article [I] "One Monad
-- to Prove Them All" by Sandra Dylus, Jan Christiansen, and Finn
-- Teegen, we have implemeted in Agda most of the idea described above
-- (section 1- 4 and annexes A.1 A.2 included)
--
-- Two main differences with the CoQ implementation presented in the
-- article above:
--
-- the termination checker algorihme in Agda seems to be more
-- restrictive than the one in Coq. Auxilliary function of some nested
-- type can hardly be used in nesting types.
--
-- Bad point : we are "forced" to inline the auxiliary functions by
-- hands.
--
-- Good point : proofs are sort of easier, the same proof schema
-- being repeated over and over again.
--
-- copyright : David Janin, LaBRI, Bordeaux INP, Bordeaux University, june 2019

module Mona where


open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Equality
open import Agda.Primitive
open import Function
open import Axiom.Extensionality.Propositional as Extensionality
open import Data.Maybe
open import Data.Product

open import Properties

-- open import Relation.Binary.EqReasoning
-- open import Size


postulate funext : ∀ {a b} -> Extensionality.Extensionality a b

data ⊥ : Set  where

data ⊤ : Set where
  tt : ⊤

-- * Containers and extensions

-- ** Definitions

data Const (B A : Set) : Set where
  cont : B -> Const B A

data Ext {l} (Shape : Set l) (Pos : Shape → Set l) (A : Set l) : Set l where
   ext : (s : Shape) -> (Pos s -> A) → Ext Shape Pos A

record Container {l} (F : Set l -> Set l) : Set (lsuc l) where
  field
    Shape : Set l
    Pos : Shape -> Set l
    to : ∀ {A : Set l} -> Ext Shape Pos A → F A
    from : ∀ {A : Set l} -> F A -> Ext Shape Pos A
    toFrom : ∀ {A : Set l} -> (fx : F A) -> to(from fx) ≡ fx
    fromTo : ∀ {A : Set l} -> (e : Ext Shape Pos A) -> from(to e) ≡ e


-- ** Instance examples

module CZero where
  open Container

  Zero : Set -> Set
  Zero A = ⊥


  instance
    CZero : Container Zero
    CZero = record {
      Shape = ⊥  ;
      Pos = λ ();
      to = toZero ; -- toZero;
      from = fromZero;
      toFrom = λ ();
      fromTo = fromToZero
      }
     where
       toZero : ∀ {A : Set} → Ext ⊥ (λ ()) A → Zero A
       toZero (ext () _)
       fromZero : ∀ {A : Set} → Zero A → Ext ⊥ (λ ()) A
       fromZero ()
       fromToZero : ∀ {A : Set} (e : Ext ⊥ (λ ()) A) → fromZero (toZero e) ≡ e
       fromToZero (ext () _)
      

module COne where
  open Container

  One : Set -> Set
  One A = ⊤


  instance
    COne : Container One
    COne = record {
      Shape = ⊤  ;
      Pos = λ _ -> ⊥;
      to = λ {A} _ → tt;
      from = λ {A} _ → ext tt (λ ());
      toFrom = λ {A} (x : One A) -> toFromOne {A} x;
      fromTo = λ {A} e -> fromToOne e
      }
      where
        -- pattern matching is not available within record
        toFromOne : ∀ {A} -> (x : One A) -> tt ≡ x
        toFromOne tt = refl
        fromToOne : ∀ {A} -> (e : Ext ⊤ ( λ _ -> ⊥) A) -> ext tt (λ ()) ≡ e
        fromToOne (ext tt _) = cong (λ x -> ext tt x) (funext λ ())

-- * Free monad

-- ** Definition

data Free {F : Set -> Set} (CF : Container F) (A : Set) : Set where
 pure : A -> Free CF A
 impure : Ext (Container.Shape CF) (Container.Pos CF) (Free CF A) -> Free CF A

-- ** Example

module MaybeF where
  open COne

  MaybeF : (A : Set) -> Set
  MaybeF A =  Free COne A

  NothingF : ∀ {A : Set} -> MaybeF A
  NothingF {A} = impure (ext tt (λ ()))
  
  JustF : ∀ {A : Set} -> A -> MaybeF A
  JustF x = pure x


-- ** Free CF is a monadic derived functions

mapF : ∀ {F CF} -> Map (Free {F} CF) -- (A -> B) -> Free {F} CF A -> Free {F} CF B
mapF f (pure x) = pure (f x)
mapF f (impure (ext s pf)) = impure (ext s (λ c -> mapF f (pf c)))


 
joinF : ∀ {F CF} ->  Join (Free {F} CF) -- Free {F} CF (Free {F} CF A) -> Free {F} CF A
joinF (pure m) = m
joinF (impure (ext s pf)) = impure (ext s (λ c -> joinF (pf c)))

returnF : ∀ {F CF} -> Return (Free {F} CF) -- A -> Free {F} CF A
returnF x = pure x

bindF :  ∀ {F : Set -> Set} {CF : Container F} 
  -> Bind (Free {F} CF)  --  ->  Free {F} CF A -> (A -> Free {F} CF B) -> Free {F} CF B
bindF (pure x) f = f x
bindF (impure (ext s pf)) f = impure (ext s (λ c -> bindF (pf c) f))

-- ** Free CF is indeed a functor

open isFunctorMap

module isFunctorFree where
  mapId : ∀ {F CF} -> MapId {Free CF} (mapF {F} {CF})
  mapId (pure x) = refl
  mapId (impure (ext s pf))
       = cong (λ x -> impure (ext s x)) (funext (λ c -> mapId (pf c)))

  mapCompose : ∀ {F CF} -> MapCompose {Free CF} (mapF {F} {CF})
  mapCompose (pure x) = refl
  mapCompose (impure (ext s pf))
        =  cong (λ x -> impure (ext s x)) (funext (λ c -> mapCompose  (pf c)))


-- ** Free CF is indeed a monad

open isMonad

returnMapF : ∀ {F CF} -> ReturnMap {Free {F} CF} mapF returnF --  (mapF {F} {CF}) (returnF {F} {CF})
returnMapF {F} {CF} x =  refl 

returnBindF : ∀ {F CF} -> ReturnBind {Free CF} (returnF {F} {CF}) (bindF {F} {CF})
returnBindF {F} {CF} x f = refl

bindReturnF : ∀ {F CF} -> BindReturn {Free CF} (returnF {F} {CF}) (bindF {F} {CF})
bindReturnF {F} {CF} (pure x) = cong (λ x -> pure x) refl
bindReturnF {F} {CF} (impure (ext s pf))
    = cong (λ c -> impure (ext s c)) (funext (λ  c -> bindReturnF (pf c)))

bindAssocF : ∀ {F CF} -> BindAssoc {Free CF} (bindF {F} {CF})
bindAssocF {F} {CF} (pure x) f g = refl
bindAssocF {F} {CF} (impure (ext s pf)) f g
    =  cong (λ c -> impure (ext s c)) (funext (λ c -> bindAssocF (pf c) f g))

mapJoinBindF :  ∀ {F CF} -> MapJoinBind {Free {F} CF} mapF joinF bindF
mapJoinBindF (pure x) f = refl
mapJoinBindF (impure (ext s pf)) f
    =  cong (λ x -> impure (ext s x)) (funext (λ c -> mapJoinBindF (pf c) f))

bindJoinF :  ∀ {F CF} -> BindJoin  {Free {F} CF} bindF joinF
bindJoinF (pure mm) = refl
bindJoinF (impure (ext s pf))
    = cong (λ x -> impure (ext s x)) (funext (λ c -> bindJoinF (pf c)))

bindReturnMapF :  ∀ {F CF} -> BindReturnMap  {Free {F} CF} bindF returnF mapF
bindReturnMapF f (pure x) = refl
bindReturnMapF f (impure (ext s pf))
    =  cong (λ x -> impure  (ext s x)) (funext (λ c ->  bindReturnMapF f (pf c)))
    
-- * Monadic list

-- ** Definition

data List {F : Set -> Set}  (CF : Container F) (A : Set) : Set where
  nil : List  CF A
  cons : A -> Free CF (List CF A) -> List  CF A


-- ** Monad lists monoid

append : ∀ {F CF} ->  Op (List {F} CF) -- List {F} CF A -> List {F} CF A -> List CF A
appendF : ∀ {F CF} ->  OpF (Free {F} CF ∘ List {F} CF) (List {F} CF) -- Free {F} CF (List CF A) -> List CF A  -> Free CF (List CF A)

append nil l2 = l2
append (cons x (pure l)) l2 = cons x (pure (append l l2))
append (cons x (impure (ext s pf))) l2
  = cons x (impure (ext s (λ c -> appendF (pf c) l2)))

appendF (pure l1) l2 = pure (append l1 l2)
appendF (impure (ext s pf)) l2 = impure (ext s (λ c -> appendF (pf c) l2))

open isMonoid

module isMonoidL where
  leftUnit :  ∀ {F} {CF : Container F} ->  LeftUnit {List CF} append nil
    -- (l : List {F} CF A) -> append nil l ≡ l
  leftUnit l = refl

  -- Right unit

  rightUnit : ∀ {F}{CF : Container F} -> RightUnit {List CF} append nil
    --  (l : List {F} CF A) -> append l nil ≡ l
  rightUnitF : ∀ {F} {CF : Container F} -> RightUnitF {(Free CF) ∘ (List CF)} appendF nil
    --  (l : Free CF (List {F} CF A)) -> appendF m nil ≡ m

  rightUnit nil = refl
  rightUnit (cons x (pure l))  rewrite (rightUnit l)  = refl
  rightUnit (cons x (impure (ext s pf)))
    = cong (λ p -> cons x (impure (ext s p))) (funext (λ c -> rightUnitF (pf c)))

  rightUnitF (pure l) = cong pure (rightUnit l)
  rightUnitF (impure (ext s pf))
   = cong (λ p -> impure (ext s p)) (funext (λ c -> rightUnitF (pf c)))

  -- Associativity

  assoc : ∀ {F}{CF : Container F} -> Assoc {List CF} append
  -- (l1 l2  l3 : List CF A) -> append l1 (append l2 l3) ≡ append (append l1 l2) l3
  assocF : ∀ {F}{CF : Container F} -> AssocF {(Free CF) ∘ (List CF)} appendF append
  -- (m : Free CF (List CF A)) -> (l2  l3 : List CF A)
  --  -> appendF m (append l2 l3) ≡ appendF (appendF m l2) l3

  assoc nil l2 l3 = refl
  assoc (cons x (pure l)) l2 l3
    = cong (λ l -> cons x (pure l)) (assoc l l2 l3)
  assoc (cons x (impure (ext s pf))) l2 l3
    = cong (λ p -> cons x (impure (ext s p)))
      (funext (λ c -> assocF (pf c) l2 l3))

  assocF (pure l) l2 l3 = cong pure (assoc l l2 l3)
  assocF (impure (ext s pf)) l2 l3
        = cong (λ p -> impure (ext s p)) (funext (λ c -> assocF (pf c) l2 l3))

-- ** Monad list functor

mapL : ∀ {F CF A B} ->  (A -> B) -> List {F} CF A -> List {F} CF B
mapLF :  ∀ {F CF A B} ->  (A -> B) -> Free {F} CF (List CF A) -> Free {F} CF (List CF B)

mapL f nil = nil
mapL f (cons x (pure l)) = cons (f x) (pure (mapL f l))
mapL f (cons x (impure (ext s p))) = cons (f x)
    (impure (ext s (λ c ->  mapLF f (p c))))

mapLF f (pure l) = pure (mapL f l)
mapLF f (impure (ext s p)) = impure (ext s (λ c -> mapLF f (p c)))
  

open isFunctorMap

module isFunctorMapList where
  mapId :  ∀ {F CF} -> MapId {List {F} CF} mapL
  mapIdF :  ∀ {F CF} -> MapId {λ A -> Free {F} CF (List CF A)} mapLF
  
  mapId nil = refl
  mapId (cons x (pure l)) = cong (λ l -> cons x (pure l)) (mapId l)
  mapId (cons x (impure (ext s pf)))
     = cong (λ p -> cons x (impure (ext s p))) (funext (λ c -> mapIdF (pf c)))

  mapIdF (pure l) = cong pure (mapId l)
  mapIdF (impure (ext s pf))
    = cong (λ p -> impure (ext s p)) (funext (λ c -> mapIdF (pf c)))

  mapCompose :  ∀ {F CF} -> MapCompose {List {F} CF} mapL
  mapComposeF :  ∀ {F CF} -> MapCompose {λ A -> Free {F} CF (List CF A)} mapLF
  
  mapCompose nil = refl
  mapCompose {f = f} {g = g} (cons x (pure l))
     =  cong (λ l -> cons ((g ∘ f) x) (pure l)) (mapCompose l)
  mapCompose {f = f} {g = g} (cons x (impure (ext s pf)))
    = cong (λ p -> cons (g(f(x))) $ impure (ext s p))
       (funext (λ c -> mapComposeF (pf c)))

  mapComposeF (pure l) = cong pure (mapCompose l)
  mapComposeF (impure (ext s pf))
    =  cong (λ p -> impure (ext s p)) (funext (λ c -> mapComposeF (pf c)))

-- * Monadic stream

-- In monadic stream, it is the monadic action that may tell if a stream is over or not.


Next : ∀ {F} {CF : Container F} -> (H : Set -> Set) -> (A : Set)  -> Set
Next {CF = CF} H A = Free CF (A × H A)

data Stream {F : Set -> Set} (CF : Container F) (A : Set) : Set where
  next : Next {F} {CF} (Stream CF) A -> Stream {F} CF A

-- ** Induced uniform semigroup


appendS : ∀ {F} {CF : Container F} {A} -> Stream CF A -> Stream CF A -> Stream CF A
appendSF : ∀ {F} {CF : Container F} {A} -> Free CF (A × Stream CF A) -> Stream CF A
  -> Free CF (A × Stream CF A)

appendS (next (pure (a , s1))) s2 = (next ∘ pure) (a , appendS s1 s2)
appendS (next (impure (ext s pf))) s2 = (next ∘ impure) (ext s (λ c -> appendSF (pf c) s2))

appendSF (pure (a , m1)) m = pure (a , appendS m1 m)
appendSF (impure (ext s pf)) m = impure (ext s (λ  c -> appendSF (pf c) m))


module isSemigroup where
  -- Associativity

  assoc : ∀ {F}{CF : Container F} ->
    Assoc {Stream CF} appendS
  -- (l1 l2  l3 : Stream CF A) ->
  --   appendS l1 (appendS l2 l3) ≡ appendS (appendS l1 l2) l3
  assocF : ∀ {F}{CF : Container F} ->
    AssocF {λ A -> Free CF (A × Stream CF A)} {Stream CF} appendSF appendS
  -- (m : Free CF (A × Stream CF A)) -> (l2  l3 : Stream CF A)
  --  -> appendSF m (appendS l2 l3) ≡ appendSF (appendSF m l2) l3

  assoc (next (pure (a , l))) l2 l3
    =  cong (λ l -> next(pure (a , l))) (assoc l l2 l3)
  assoc (next (impure (ext s pf))) l2 l3
    = cong (λ p -> next(impure (ext s p))) (funext (λ c -> assocF (pf c) l2 l3))
    
  assocF (pure (a , l)) l2 l3 = cong (λ l -> pure (a , l)) (assoc l l2 l3)
  assocF (impure (ext s pf)) l2 l3
        = cong (λ p -> impure (ext s p)) (funext (λ c -> assocF (pf c) l2 l3))


mapS : ∀ {F CF A B} -> (A -> B) -> Stream {F} CF A -> Stream CF B
mapSF : ∀ {F CF A B} -> (A -> B) -> Free {F} CF (A × Stream CF A)
    -> Free {F} CF (B × Stream CF B)

mapS f (next (pure (fst , snd))) = next (pure (f fst ,  mapS f snd))
mapS f (next (impure (ext s pf)))
   =  next (impure (ext s (λ c -> mapSF f (pf c))))

mapSF f (pure (fst , snd)) = pure (f fst , mapS f snd)
mapSF f (impure (ext s pf)) =  impure (ext s (λ  c -> mapSF f (pf c))) 

module isFunctorMapStream where
  mapId :  ∀ {F CF} -> MapId {Stream {F} CF} mapS
  mapIdF :  ∀ {F CF} -> MapId {λ A -> Free {F} CF (A × Stream CF A)} mapSF
  
  mapId (next (pure (a , l))) = cong (λ l -> next (pure (a ,  l))) (mapId l)
  mapId (next (impure (ext s pf)))
     = cong (λ p -> next (impure (ext s p))) (funext (λ c -> mapIdF (pf c)))

  mapIdF (pure (a , l)) =  cong (λ l -> pure (a , l)) (mapId l)
  mapIdF (impure (ext s pf))
    = cong (λ p -> impure (ext s p)) (funext (λ c -> mapIdF (pf c)))

  mapCompose :  ∀ {F CF} -> MapCompose {Stream {F} CF} mapS
  mapComposeF :  ∀ {F CF} -> MapCompose {λ A -> Free {F} CF (A × Stream CF A)} mapSF
  
  mapCompose {f = f} {g = g} (next (pure (x , l)))
    =  cong (λ l -> next (pure $ (g ∘ f) x , l)) (mapCompose l)
  mapCompose  (next (impure (ext s pf)))
    = cong (λ p -> next(impure (ext s p))) (funext (λ c -> mapComposeF (pf c)))

  mapComposeF {f = f} {g = g} (pure (a , l))
     = cong (λ l -> pure (g (f(a)) , l) ) (mapCompose l)
  mapComposeF (impure (ext s pf))
    =  cong (λ p -> impure (ext s p)) (funext (λ c -> mapComposeF (pf c)))

-- ** Monad folding (quite a mindless translation of [I])

foldF :  ∀ {A B : Set} {F : Set -> Set} {CF : Container F}
  -> (A -> B) -> (F B  -> B) -> Free {F} CF A -> B
foldF f g (pure x) = f x
foldF {CF = CF} f g (impure (ext s pf))
  = g (Container.to CF (ext s (λ c -> (foldF f g) (pf c))))

induce : ∀ {M F : Set -> Set} {CF : Container F} ->
   Return M -> Join M -> (A : Set) -> (f : (X : Set) -> F X → M X) -> Free CF A  -> M A
induce {M} {F} return join A f m
  = foldF return (λ x -> join (f (M A) x)) m

Id : Set -> Set
Id A = A

open CZero

zero-to-id : (A : Set) -> Zero A -> Id A
zero-to-id A ()


free-to-id : (A : Set) -> (Free CZero A) -> Id A
free-to-id A m = induce id id A zero-to-id m

open COne

one-to-maybe : (A : Set) -> One A -> Maybe A
one-to-maybe A _ = nothing


joinMaybe : ∀ {A : Set} -> Maybe (Maybe A) -> Maybe A
joinMaybe nothing = nothing
joinMaybe (just nothing) = nothing
joinMaybe (just (just x)) = just x

free-to-maybe : (A : Set) -> (Free COne A) -> Maybe A
free-to-maybe A m = induce (just) (joinMaybe) A one-to-maybe m
