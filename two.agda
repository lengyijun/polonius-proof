module polonius-abella.two where
open import Data.Sum -- _⊎_ \uplus
open import Relation.Nullary
open import Data.Product

data Origin : Set where
data Loan : Set where
data Point : Set where

data origin_live_on_entry ( o : Origin )( p : Point ) :  Set where
data loan_issued_at ( o : Origin )( l : Loan )( p : Point ) : Set where
data cfg_edge ( p1 p2 : Point ) : Set where
data loan_invalidated_at ( l : Loan )( p : Point ) : Set where  
data not_loan_killed_at ( l : Loan )( p : Point ) : Set where
data subset_base ( o1 o2 : Origin) (p : Point) : Set where


-- TODO rename
OriginLiveAxiom : Origin -> Point -> Set
OriginLiveAxiom o p = origin_live_on_entry o p  ⊎  ¬ origin_live_on_entry o p

data naive_subset (o1 o3 : Origin) (p2 : Point ):  Set where
  con1 : subset_base o1 o3 p2 -> naive_subset o1 o3 p2
  con2 : Σ[ p1 ∈ Point  ] naive_subset o1 o3 p1 × cfg_edge p1 p2 × origin_live_on_entry o1 p2 × origin_live_on_entry o3 p2 -> naive_subset o1 o3 p2
  con3 : Σ[ o2 ∈ Origin ] naive_subset o1 o2 p2 × naive_subset o2 o3 p2 -> naive_subset o1 o3 p2
 
data naive_origin_contains_loan_on_entry (o2 : Origin) (l : Loan) (p2 :  Point ) : Set where
  con1 : loan_issued_at o2 l p2 -> naive_origin_contains_loan_on_entry o2 l p2
  con2 : Σ[ o1 ∈ Origin ] naive_origin_contains_loan_on_entry o1 l p2 × naive_subset o1 o2 p2 -> naive_origin_contains_loan_on_entry o2 l p2
  con3 : Σ[ p1 ∈ Point ] naive_origin_contains_loan_on_entry o2 l p1 × not_loan_killed_at l p1 × cfg_edge p1 p2 × origin_live_on_entry o2 p2 -> naive_origin_contains_loan_on_entry o2 l p2
  
data naive_loan_live_at (l : Loan)(p : Point) : Set where
  con : Σ[ o ∈ Origin ] naive_origin_contains_loan_on_entry o l p × origin_live_on_entry o p -> naive_loan_live_at l p

data naive_errors (l : Loan) (p : Point ) : Set where
  con : loan_invalidated_at l p ->  naive_loan_live_at l p -> naive_errors l p
  
data dead_borrow_region_can_reach_root (o : Origin ) (p : Point ) (l : Loan) : Set  where
  con : loan_issued_at o l p -> ¬ origin_live_on_entry o p -> dead_borrow_region_can_reach_root o p l

data dead_borrow_region_can_reach_dead (o2 : Origin) (p : Point ) (l : Loan ) : Set
data dying_region_requires (o : Origin) (p1 p2 : Point ) (l : Loan ) : Set
data live_to_dying_regions (o1 o2 : Origin ) (p1 p2 : Point ) : Set
data dying_can_reach_origins (o : Origin )(p1 p2 : Point ) : Set 
data dying_can_reach (o1 o2 : Origin )(p1 p2 : Point) : Set 
data dying_can_reach_live (o1 o2 : Origin )(p1 p2 : Point) : Set
data datafrog_opt_subset (o1 o2 : Origin)(p : Point) : Set
data datafrog_opt_origin_contains_loan_on_entry (o : Origin)(l : Loan)(p : Point) : Set
data datafrog_opt_loan_live_at (l : Loan )(p : Point) : Set 

data dead_borrow_region_can_reach_dead o2 p l where
  con1 : dead_borrow_region_can_reach_root o2 p l -> dead_borrow_region_can_reach_dead o2 p l
  con2 : Σ[ o1 ∈ Origin ] dead_borrow_region_can_reach_dead o1 p l × datafrog_opt_subset o1 o2 p × ¬ origin_live_on_entry o2 p -> dead_borrow_region_can_reach_dead o2 p l

data dying_region_requires o p1 p2 l where
  con : datafrog_opt_origin_contains_loan_on_entry o l p1 -> not_loan_killed_at l p1 -> cfg_edge p1 p2 -> ¬ origin_live_on_entry o p2 -> dying_region_requires o p1 p2 l

data live_to_dying_regions o1 o2 p1 p2 where
  con : datafrog_opt_subset o1 o2 p1 -> cfg_edge p1 p2 -> origin_live_on_entry o1 p2 -> ¬ origin_live_on_entry  o2  p2 -> live_to_dying_regions o1 o2 p1 p2

data dying_can_reach_origins o2 p1 p2 where
  con1 : Σ[ o1 ∈ Origin ] live_to_dying_regions o1 o2 p1 p2 -> dying_can_reach_origins o2 p1 p2
  con2 : Σ[ l ∈ Loan ] dying_region_requires o2 p1 p2 l -> dying_can_reach_origins o2 p1 p2

data dying_can_reach o1 o3 p1 p2 where
  con1 : dying_can_reach_origins o1 p1 p2 -> datafrog_opt_subset o1 o3 p1 -> dying_can_reach o1 o3 p1 p2
  con2 : Σ[ o2 ∈ Origin ] dying_can_reach o1 o2 p1 p2 × ¬ origin_live_on_entry o2 p2 × datafrog_opt_subset o2 o3 p1 -> dying_can_reach o1 o3 p1 p2

data dying_can_reach_live o1 o2 p1 p2 where
  con : dying_can_reach o1 o2 p1 p2 -> origin_live_on_entry o2 p2 -> dying_can_reach_live o1 o2 p1 p2

data datafrog_opt_subset o1 o3 p2 where
  con1 : subset_base o1 o3 p2 -> datafrog_opt_subset o1 o3 p2
  con2 : Σ[ p1 ∈ Point ] datafrog_opt_subset o1 o3 p1 × cfg_edge p1 p2 × origin_live_on_entry o1 p2 × origin_live_on_entry o3 p2 -> datafrog_opt_subset o1 o3 p2
  con3 : Σ[ p1 ∈ Point ] Σ[ o2 ∈ Origin ] live_to_dying_regions o1 o2 p1 p2 × dying_can_reach_live o2  o3 p1 p2 -> datafrog_opt_subset o1 o3 p2

data datafrog_opt_origin_contains_loan_on_entry o2 l p2 where
  con1 : loan_issued_at o2 l p2 -> datafrog_opt_origin_contains_loan_on_entry o2 l p2
  con2 : Σ[ p1 ∈ Point ] datafrog_opt_origin_contains_loan_on_entry o2  l p1 × not_loan_killed_at l p1 × cfg_edge p1 p2 × origin_live_on_entry o2 p2 -> datafrog_opt_origin_contains_loan_on_entry o2 l p2
  con3 : Σ[ p1 ∈ Point ] Σ[ o1 ∈ Origin ] dying_region_requires o1 p1 p2 l × dying_can_reach_live o1 o2 p1 p2 -> datafrog_opt_origin_contains_loan_on_entry o2 l p2

data datafrog_opt_loan_live_at l p where
  con1 : Σ[ o ∈ Origin ]  datafrog_opt_origin_contains_loan_on_entry o l p × origin_live_on_entry o p -> datafrog_opt_loan_live_at l p
  con2 : Σ[ o1 ∈ Origin ] Σ[ o2 ∈ Origin ] dead_borrow_region_can_reach_dead o1 p l × datafrog_opt_subset o1 o2 p × origin_live_on_entry o2 p -> datafrog_opt_loan_live_at l p

data datafrog_opt_errors (l : Loan)( p : Point ) : Set where
  con : loan_invalidated_at l p ->  datafrog_opt_loan_live_at l p -> datafrog_opt_errors l p
