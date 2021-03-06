open import Data.Sum
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Nullary

postulate
  Origin : Set
  Loan : Set
  Point : Set
  origin-live-on-entry : Origin -> Point -> Set
  loan-issued-at : Origin -> Loan -> Point -> Set
  cfg-edge : Point -> Point -> Set
  loan-invalidated-at : Loan -> Point -> Set
  not-loan-killed-at :  Loan -> Point -> Set
  subset-base : Origin -> Origin -> Point -> Set

data naive-subset (o1 o3 : Origin) (p2 : Point ):  Set where
  base : subset-base o1 o3 p2 -> naive-subset o1 o3 p2
  propagate : Σ[ p1 ∈ Point  ] naive-subset o1 o3 p1 × cfg-edge p1 p2 × origin-live-on-entry o1 p2 × origin-live-on-entry o3 p2 -> naive-subset o1 o3 p2
  concat : Σ[ o2 ∈ Origin ] naive-subset o1 o2 p2 × naive-subset o2 o3 p2 -> naive-subset o1 o3 p2
 
data naive-origin-contains-loan-on-entry (o2 : Origin) (l : Loan) (p2 :  Point ) : Set where
  con1 : loan-issued-at o2 l p2 -> naive-origin-contains-loan-on-entry o2 l p2
  con2 : Σ[ o1 ∈ Origin ] naive-origin-contains-loan-on-entry o1 l p2 × naive-subset o1 o2 p2 -> naive-origin-contains-loan-on-entry o2 l p2
  con3 : Σ[ p1 ∈ Point ] naive-origin-contains-loan-on-entry o2 l p1 × not-loan-killed-at l p1 × cfg-edge p1 p2 × origin-live-on-entry o2 p2 -> naive-origin-contains-loan-on-entry o2 l p2
  
data naive-loan-live-at (l : Loan)(p : Point) : Set where
  con : Σ[ o ∈ Origin ] naive-origin-contains-loan-on-entry o l p × origin-live-on-entry o p -> naive-loan-live-at l p

data naive-errors (l : Loan) (p : Point ) : Set where
  con : loan-invalidated-at l p ->  naive-loan-live-at l p -> naive-errors l p
  
data dead-borrow-region-can-reach-root (o : Origin ) (p : Point ) (l : Loan) : Set  where
  con : loan-issued-at o l p -> ¬ origin-live-on-entry o p -> dead-borrow-region-can-reach-root o p l

data dead-borrow-region-can-reach-dead (o2 : Origin) (p : Point ) (l : Loan ) : Set
data dying-region-requires (o : Origin) (p1 p2 : Point ) (l : Loan ) : Set
data live-to-dying-regions (o1 o2 : Origin ) (p1 p2 : Point ) : Set
data dying-can-reach-origins (o : Origin )(p1 p2 : Point ) : Set 
data dying-can-reach (o1 o2 : Origin )(p1 p2 : Point) : Set 
data dying-can-reach-live (o1 o2 : Origin )(p1 p2 : Point) : Set
data datafrog-opt-subset (o1 o2 : Origin)(p : Point) : Set
data datafrog-opt-origin-contains-loan-on-entry (o : Origin)(l : Loan)(p : Point) : Set
data datafrog-opt-loan-live-at (l : Loan )(p : Point) : Set 

data dead-borrow-region-can-reach-dead o2 p l where
  con1 : dead-borrow-region-can-reach-root o2 p l -> dead-borrow-region-can-reach-dead o2 p l
  con2 : Σ[ o1 ∈ Origin ] dead-borrow-region-can-reach-dead o1 p l × datafrog-opt-subset o1 o2 p × ¬ origin-live-on-entry o2 p -> dead-borrow-region-can-reach-dead o2 p l

data dying-region-requires o p1 p2 l where
  con : datafrog-opt-origin-contains-loan-on-entry o l p1 -> not-loan-killed-at l p1 -> cfg-edge p1 p2 -> ¬ origin-live-on-entry o p2 -> dying-region-requires o p1 p2 l

data live-to-dying-regions o1 o2 p1 p2 where
  con : datafrog-opt-subset o1 o2 p1 -> cfg-edge p1 p2 -> origin-live-on-entry o1 p2 -> ¬ origin-live-on-entry o2 p2 -> live-to-dying-regions o1 o2 p1 p2

data dying-can-reach-origins o2 p1 p2 where
  con1 : Σ[ o1 ∈ Origin ] live-to-dying-regions o1 o2 p1 p2 -> dying-can-reach-origins o2 p1 p2
  con2 : Σ[ l ∈ Loan ] dying-region-requires o2 p1 p2 l -> dying-can-reach-origins o2 p1 p2

data dying-can-reach o1 o3 p1 p2 where
  con1 : dying-can-reach-origins o1 p1 p2 -> datafrog-opt-subset o1 o3 p1 -> dying-can-reach o1 o3 p1 p2
  con2 : Σ[ o2 ∈ Origin ] dying-can-reach o1 o2 p1 p2 × ¬ origin-live-on-entry o2 p2 × datafrog-opt-subset o2 o3 p1 -> dying-can-reach o1 o3 p1 p2

data dying-can-reach-live o1 o2 p1 p2 where
  con : dying-can-reach o1 o2 p1 p2 -> origin-live-on-entry o2 p2 -> dying-can-reach-live o1 o2 p1 p2

data datafrog-opt-subset o1 o3 p2 where
  base : subset-base o1 o3 p2 -> datafrog-opt-subset o1 o3 p2
  propagate : Σ[ p1 ∈ Point ] datafrog-opt-subset o1 o3 p1 × cfg-edge p1 p2 × origin-live-on-entry o1 p2 × origin-live-on-entry o3 p2 -> datafrog-opt-subset o1 o3 p2
  con3 : Σ[ p1 ∈ Point ] Σ[ o2 ∈ Origin ] live-to-dying-regions o1 o2 p1 p2 × dying-can-reach-live o2 o3 p1 p2 -> datafrog-opt-subset o1 o3 p2

data datafrog-opt-origin-contains-loan-on-entry o2 l p2 where
  con1 : loan-issued-at o2 l p2 -> datafrog-opt-origin-contains-loan-on-entry o2 l p2
  con2 : Σ[ p1 ∈ Point ] datafrog-opt-origin-contains-loan-on-entry o2  l p1 × not-loan-killed-at l p1 × cfg-edge p1 p2 × origin-live-on-entry o2 p2 -> datafrog-opt-origin-contains-loan-on-entry o2 l p2
  con3 : Σ[ p1 ∈ Point ] Σ[ o1 ∈ Origin ] dying-region-requires o1 p1 p2 l × dying-can-reach-live o1 o2 p1 p2 -> datafrog-opt-origin-contains-loan-on-entry o2 l p2

data datafrog-opt-loan-live-at l p where
  con1 : Σ[ o ∈ Origin ]  datafrog-opt-origin-contains-loan-on-entry o l p × origin-live-on-entry o p -> datafrog-opt-loan-live-at l p
  con2 : Σ[ o1 ∈ Origin ] Σ[ o2 ∈ Origin ] dead-borrow-region-can-reach-dead o1 p l × datafrog-opt-subset o1 o2 p × origin-live-on-entry o2 p -> datafrog-opt-loan-live-at l p

data datafrog-opt-errors (l : Loan)( p : Point ) : Set where
  con : loan-invalidated-at l p -> datafrog-opt-loan-live-at l p -> datafrog-opt-errors l p

mutual
  lemma1 : ∀ {o1 o9 : Origin } {p2 : Point} -> datafrog-opt-subset o1 o9 p2 -> naive-subset o1 o9 p2
  lemma1 (base x) = base x
  lemma1 (propagate (p1 , fst₁ , p1p2 , fst₃ , snd)) = propagate ( p1 , lemma1 fst₁ , p1p2 , fst₃ , snd )
  lemma1 (con3 (p1 , o3 , con x p1p2 x₂ x₃ , con x₁ x₄)) = propagate ( p1 , concat ( o3 , lemma1 x , lemma2 x₁ ) , p1p2 , x₂ , x₄ )

  lemma2 : ∀ {o1 o9 : Origin } {p1 p2 : Point} -> dying-can-reach o1 o9 p1 p2 -> naive-subset o1 o9 p1
  lemma2 (con1 x x₁) = lemma1 x₁
  lemma2 (con2 (o2 , fst₁ , fst₂ , snd)) = concat ( o2 , lemma2 fst₁ , lemma1 snd )

lemma3 : ∀ {o2 : Origin}{l : Loan}{p2 : Point} -> datafrog-opt-origin-contains-loan-on-entry o2 l p2 -> naive-origin-contains-loan-on-entry o2 l p2
lemma3 (con1 x) = con1 x
lemma3 (con2 (p1 , fst , fst₂ , fst₃ , snd)) = con3 (p1 , lemma3 fst , fst₂ , fst₃ , snd )
lemma3 (con3 (p1 , o1 , con x x₁ x₂ x₃ , con x₄ x₅)) = con3 (p1 , con2 ( o1 , lemma3 x , lemma2 x₄ ) , x₁ , x₂ , x₅ )

lemma4 : ∀ {o2 : Origin}{l : Loan}{p : Point} -> dead-borrow-region-can-reach-dead o2 p l -> naive-origin-contains-loan-on-entry o2 l p
lemma4 (con1 (con x x₁)) = con1 x
lemma4 (con2 (o1 , fst , fst₁ , snd)) = con2 ( o1 , lemma4 fst , lemma1 fst₁ )

datafrog→naive : ∀{l : Loan}{p : Point} ->  datafrog-opt-errors l p -> naive-errors l p
datafrog→naive (con x (con1 (o , fst , snd))) = con x ( con ( o , lemma3 fst , snd  ) )
datafrog→naive (con x (con2 (o1 , o2 , fst₁ , fst₂ , snd))) = con x ( con ( o2 , con2 ( o1 , lemma4 fst₁ , lemma1 fst₂ )  , snd ) )

data my-subset (o1 o3 : Origin)(p : Point) : Set where
  con1 : datafrog-opt-subset o1 o3 p -> my-subset o1 o3 p
  con2 : Σ[ o2 ∈ Origin ] datafrog-opt-subset o1 o2 p × my-subset o2 o3 p -> my-subset o1 o3 p
  
my-subset-concat : ∀{o1 o8 o9 : Origin}{p : Point} -> my-subset o1 o8 p -> my-subset o8 o9 p -> my-subset o1 o9 p
my-subset-concat {o1} {o8} {o9} (con1 x) x₁ = con2 (o8 , x , x₁)
my-subset-concat (con2 (o2 , fst , snd)) x₁ = con2 (o2 , fst , my-subset-concat snd x₁)

data my-origin-contains-loan-on-entry(o2 : Origin)(l : Loan)(p : Point) : Set where
  con1 : datafrog-opt-origin-contains-loan-on-entry o2 l p -> my-origin-contains-loan-on-entry o2 l p
  con2 : Σ[ o1 ∈ Origin ] my-origin-contains-loan-on-entry o1 l p × datafrog-opt-subset o1 o2 p -> my-origin-contains-loan-on-entry o2 l p
  
postulate
  -- TODO rename
  OriginLiveAxiom : (o : Origin) -> ( p : Point ) -> origin-live-on-entry o p  ⊎  ¬ origin-live-on-entry o p

mutual
  lemma14 :  ∀{o1 o2 o9 : Origin}{p1 p2 : Point} -> dying-can-reach o1 o2 p1 p2 -> my-subset o2 o9 p1 -> cfg-edge p1 p2 -> origin-live-on-entry o9 p2 -> dying-can-reach-live o1 o9 p1 p2 ⊎ Σ[ o2 ∈ Origin ] dying-can-reach-live o1 o2 p1 p2 × my-subset o2 o9 p2
  lemma14 {o1} {o2} {o9} {p1} {p2} x x₁ x₂ x₃ with OriginLiveAxiom o2 p2
  lemma14 {o1} {o2} {o9} {p1} {p2} x x₁ x₂ x₃ | inj₁ x₄ = inj₂ ( o2 , con x x₄ , my-subset-propagate x₁ x₂ x₄ x₃ )
  lemma14 {o1} {o2} {o9} {p1} {p2} x (con1 x₁) p1p2 x₃ | inj₂ y = inj₁ (con (con2 (o2 , x , y , x₁)) x₃)
  lemma14 {o1} {o2} {o9} {p1} {p2} x (con2 (o3 , fst , snd)) p1p2 x₃ | inj₂ y = lemma14 ( con2 ( o2 ,  x , y , fst) ) snd p1p2 x₃
  
  lemma15 : ∀{o1 o9 : Origin}{p1 p2 : Point} -> my-subset o1 o9 p1 -> dying-can-reach-origins o1 p1 p2 -> cfg-edge p1 p2 -> ¬ origin-live-on-entry o1 p2 -> origin-live-on-entry o9 p2 -> dying-can-reach-live o1 o9 p1 p2 ⊎ Σ[ o2 ∈ Origin ] dying-can-reach-live o1 o2 p1 p2 × my-subset o2 o9 p2
  lemma15 (con1 x) y x₁ x₂ x₃ = inj₁ (con (con1 y x) x₃)
  lemma15 {p2 = p2} (con2 (o2 , fst , snd)) y x₁ x₂ x₃ with OriginLiveAxiom o2 p2
  lemma15 {p2 = p2} (con2 (o2 , fst , snd)) y x₁ x₂ x₃ | inj₁ x = inj₂ ( o2 , con ( con1 y fst ) x , my-subset-propagate snd x₁ x x₃ )
  lemma15 {p2 = p2} (con2 (o2 , fst , snd)) y x₁ x₂ x₃ | inj₂ y₁ = lemma14 (con1 y fst) snd x₁ x₃

  my-subset-propagate : ∀{o1 o9 : Origin}{p1 p2 : Point} -> my-subset o1 o9 p1 -> cfg-edge p1 p2 -> origin-live-on-entry o1 p2 -> origin-live-on-entry o9 p2 -> my-subset o1 o9 p2
  my-subset-propagate {p1 = p1} (con1 x) p1p2 x₂ x₃ = con1 (propagate (p1 , x , p1p2 , x₂ , x₃ ))
  my-subset-propagate {p2 = p2} (con2 (o2 , fst , snd)) p1p2 x₂ x₃ with OriginLiveAxiom o2 p2
  my-subset-propagate {p1 = p1} {p2 = p2} (con2 (o2 , fst , snd)) p1p2 x₂ x₃ | inj₁ x = my-subset-concat (con1 (propagate (p1 , fst , p1p2 , x₂ , x ))) ( my-subset-propagate snd p1p2 x x₃ )
  my-subset-propagate {o1} {o9} {p1} {p2} (con2 (o2 , fst , snd)) p1p2 x₂ x₃ | inj₂ y with lemma15 snd (con1 (o1 , con fst p1p2 x₂ y)) p1p2 y x₃
  my-subset-propagate {o1} {o9} {p1} {p2} (con2 (o2 , fst , snd)) p1p2 x₂ x₃ | inj₂ y | inj₁ y₁ = con1 (con3 ( p1 , o2 , con fst p1p2 x₂ y , y₁ ))
  my-subset-propagate {o1} {o9} {p1} {p2} (con2 (o2 , fst , snd)) p1p2 x₂ x₃ | inj₂ y | inj₂ (o3 , con x x₁ , snd₁) = con2 ( o3 , con3 (p1 , o2 , con fst p1p2 x₂ y , con x x₁) , snd₁ ) 

lemma5 : ∀{o1 o3 : Origin}{p2 : Point} -> naive-subset o1 o3 p2 -> my-subset o1 o3 p2
lemma5 (base x) = con1 (base x)
lemma5 (propagate (p1 , fst , p1p2 , fst₂ , snd)) = my-subset-propagate (lemma5 fst) p1p2 fst₂ snd
lemma5 (concat (o2 , fst , snd)) = my-subset-concat (lemma5 fst) (lemma5 snd)

lemma7 : ∀{o1 o9 : Origin}{l : Loan}{p : Point} -> my-origin-contains-loan-on-entry o1 l p -> my-subset o1 o9 p ->  my-origin-contains-loan-on-entry o9 l p
lemma7 {o1} {o9} {l} {p} x (con1 x₁) = con2 (o1 , x , x₁) 
lemma7 {o1} {o9} {l} {p} x (con2 (o2 , fst , snd)) = lemma7 (con2 (o1 , x , fst)) snd

mutual
  lemma8 :  ∀{o2 o9 : Origin}{l : Loan}{p1 p2 : Point} ->
                 my-origin-contains-loan-on-entry o2 l p1 ->
                 my-subset o2 o9 p1 ->
                 cfg-edge p1 p2 ->
                 ¬ origin-live-on-entry o2 p2 ->
                 origin-live-on-entry o9 p2 ->
                 not-loan-killed-at l p1 ->
                 my-origin-contains-loan-on-entry o9 l p2
  lemma8 {o2} {o9} {l} {p1} {p2} (con1 x) x₁ p1p2 x₃ x₄ x₅ with lemma15 x₁ (con2 (l , con x x₅ p1p2 x₃)) p1p2 x₃ x₄
  lemma8 {o2} {o9} {l} {p1} {p2} (con1 x) x₁ p1p2 x₃ x₄ x₅ | inj₁ x₂ = con1 (con3 (p1 , o2 , con x x₅ p1p2 x₃ , x₂))
  lemma8 {o2} {o9} {l} {p1} {p2} (con1 x) x₁ p1p2 x₃ x₄ x₅ | inj₂ (o5 , fst , snd) = lemma7 (con1 (con3 (p1 , o2 , con x x₅ p1p2 x₃ , fst ))) snd
  lemma8 {o2} {o9} {l} {p1} {p2} (con2 (o1 , fst , snd)) x₁ p1p2 x₃ x₄ x₅ with OriginLiveAxiom o1 p2
  lemma8 {o2} {o9} {l} {p1} {p2} (con2 (o1 , fst , snd)) x₁ p1p2 x₃ x₄ x₅ | inj₁ x = lemma7 (my-origin-propagate fst p1p2 x x₅) (my-subset-propagate (con2 (o2 , snd , x₁)) p1p2 x x₄)
  lemma8 {o2} {o9} {l} {p1} {p2} (con2 (o1 , fst , snd)) x₁ p1p2 x₃ x₄ x₅ | inj₂ y = lemma8 fst (con2 (o2 , snd , x₁)) p1p2 y x₄ x₅
  
  my-origin-propagate : ∀{o2 : Origin}{l : Loan}{p1 p2 : Point} -> my-origin-contains-loan-on-entry o2 l p1 -> cfg-edge p1 p2 -> origin-live-on-entry o2 p2 -> not-loan-killed-at l p1 -> my-origin-contains-loan-on-entry o2 l p2
  my-origin-propagate {p1 = p1} (con1 x) x₁ x₂ x₃ = con1 (con2 (p1 , x , x₃ , x₁ , x₂))
  my-origin-propagate {p2 = p2} (con2 (o1 , fst , snd)) x₁ x₂ x₃ with OriginLiveAxiom o1 p2
  my-origin-propagate {p1 = p1} {p2 = p2} (con2 (o1 , fst , snd)) x₁ x₂ x₃ | inj₁ x = con2 (o1 , my-origin-propagate fst x₁ x x₃ , propagate (p1 , snd , x₁ , x , x₂) )
  my-origin-propagate {o2} {l} {p1} {p2} (con2 (o1 , fst , snd)) p1p2 x₂ x₃ | inj₂ y = lemma8 fst (con1 snd) p1p2 y x₂ x₃

lemma6 : ∀{o2 : Origin}{l : Loan}{p2 : Point} -> naive-origin-contains-loan-on-entry o2 l p2 -> my-origin-contains-loan-on-entry o2 l p2
lemma6 {o2} {l} {p2} (con1 x) = con1 (con1 x)
lemma6 {o2} {l} {p2} (con2 (o1 , fst , snd)) = lemma7 (lemma6 fst) (lemma5 snd)
lemma6 {o2} {l} {p2} (con3 (p1 , fst , fst₁ , fst₂ , snd)) = my-origin-propagate (lemma6 fst) fst₂ snd fst₁

lemma12 :  ∀{l : Loan}{p : Point}{o2 o9 : Origin } ->
           dead-borrow-region-can-reach-dead o2 p l ->
           ¬ origin-live-on-entry o2 p ->
           my-subset o2 o9 p ->
           origin-live-on-entry o9 p ->
           datafrog-opt-loan-live-at l p
lemma12 {l} {p} {o2} {o9} x x₁ (con1 x₂) x₃ = con2 (o2 , o9 , x , x₂ , x₃)
lemma12 {l} {p} {o2} {o9} x x₁ (con2 (o3 , snd)) x₃ with OriginLiveAxiom o3 p
lemma12 {l} {p} {o2} {o9} x x₁ (con2 (o3 , fst , snd)) x₃ | inj₁ x₂ = con2 (o2 , o3 , x , fst , x₂)
lemma12 {l} {p} {o2} {o9} x x₁ (con2 (o3 , fst , snd)) x₃ | inj₂ y = lemma12 (con2 (o2 , x , fst , y)) y snd x₃

mutual
  lemma11 :  ∀{l : Loan}{p : Point}{o8 o9 : Origin } ->
           my-origin-contains-loan-on-entry o8 l p ->
           my-subset o8 o9 p ->
           origin-live-on-entry o9 p ->
           ¬ origin-live-on-entry o8 p ->
           datafrog-opt-loan-live-at l p
  lemma11 {l} {p} {o8} {o9} (con1 (con1 x)) x₁ x₂ x₃ = lemma12 (con1 (con x x₃)) x₃ x₁ x₂
  lemma11 {l} {p2} {o8} {o9} (con1 (con2 (p1 , fst₁ , fst₂ , p1p2 , snd))) x₁ x₂ x₃ = con1 (o8 , con2 (p1 , fst₁ , fst₂ , p1p2 , snd) , snd)
  lemma11 {l} {p2} {o8} {o9} (con1 (con3 (p1 , o7 , con x₅ x₆ x₇ x₈ , con x x₄))) x₁ x₂ x₃ = con1
                                                                                               (o8 , con3 (p1 , o7 , con x₅ x₆ x₇ (λ _ → x₃ x₄) , con x x₄) , x₄)
  lemma11 {l} {p} {o8} {o9} (con2 (o7 , fst , snd)) x₁ x₂ x₃ with OriginLiveAxiom o7 p
  lemma11 {l} {p} {o8} {o9} (con2 (o7 , fst , snd)) x₁ x₂ x₃ | inj₁ x = lemma10 fst x
  lemma11 {l} {p} {o8} {o9} (con2 (o7 , fst , snd)) x₁ x₂ x₃ | inj₂ y = lemma11 fst (con2 (o8 , snd , x₁)) x₂ y
  
  lemma10 : ∀{l : Loan}{p : Point}{o9 : Origin } ->
           my-origin-contains-loan-on-entry o9 l p ->
           origin-live-on-entry o9 p ->
           datafrog-opt-loan-live-at l p
  lemma10 {l} {p} {o9} (con1 x) x₁ = con1 (o9 , x , x₁)
  lemma10 {l} {p} {o9} (con2 (o8 , fst , snd)) x₁ with OriginLiveAxiom o8 p
  lemma10 {l} {p} {o9} (con2 (o8 , fst , snd)) x₁ | inj₁ x = lemma10 fst x 
  lemma10 {l} {p} {o9} (con2 (o8 , fst , snd)) x₁ | inj₂ y = lemma11 fst (con1 snd) x₁ y

naive→datafrog :  ∀{l : Loan}{p2 : Point} -> naive-errors l p2  ->  datafrog-opt-errors l p2
naive→datafrog (con x (con (fst , fst₁ , snd))) = con x (lemma10 (lemma6 fst₁) snd)
