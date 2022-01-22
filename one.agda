module polonius-abella.one where
open import Data.Sum -- _⊎_ \uplus
open import Relation.Nullary

data Origin : Set where
data Loan : Set where
data Point : Set where

data origin_live_on_entry :  Origin -> Point -> Set where
data loan_issued_at : Origin -> Loan -> Point -> Set where
data cfg_edge : Point -> Point -> Set where
data loan_invalidated_at : Loan -> Point -> Set where                                                                                        
data not_loan_killed_at : Loan -> Point -> Set where
data subset_base : Origin -> Origin -> Point -> Set where


-- TODO rename
OriginLiveAxiom : Origin -> Point -> Set
OriginLiveAxiom o p = origin_live_on_entry o p  ⊎  ¬ origin_live_on_entry o p

data dead_borrow_region_can_reach_root : Origin ->  Point -> Loan -> Set where
  con : { o : Origin }{ l : Loan }{ p : Point } -> loan_issued_at o l p -> ¬ ( origin_live_on_entry o p ) -> dead_borrow_region_can_reach_root o p l


data dead_borrow_region_can_reach_dead : Origin -> Point -> Loan -> Set where
  con : { o : Origin } { l : Loan } { p : Point } -> dead_borrow_region_can_reach_root o p l -> dead_borrow_region_can_reach_dead o p l
