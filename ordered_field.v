(*
  This module defines the Ordered Field record type which can be used
  to represent algebraic ordered fields and provides a collection
  of axioms and theorems describing them.
*)

Require Import base.
Require Import group.
Require Import abelian_group.
Require Import ring.
Require Import commutative_ring.
Require Import field.

Structure Ordered_Field : Type := ordered_field {
  E: Set;
  E_0: E;
  E_1: E;

  sum: E -> E -> E;

  prod: E -> E -> E;

  lt: E -> E -> Prop;

  sum_is_assoc : is_assoc E sum;

  sum_is_comm : is_comm E sum;

  sum_is_id_l
    :  E -> Prop
    := fun x : E => is_id_l E sum x;

  sum_is_id_r
    :  E -> Prop
    := fun x : E => is_id_r E sum x;

  sum_is_id 
    :  E -> Prop
    := fun x : E => is_id E sum x;

  sum_id_l : sum_is_id_l E_0;

  sum_id_r
    :  sum_is_id_r E_0
    := fun x : E
         =>  (sum_id_l x)
         =|= (fun a => a = x) by (sum_is_comm x E_0);

  sum_id
    :  sum_is_id E_0
    := conj sum_id_l sum_id_r;

  sum_is_inv_l
    :  forall x y : E, Prop
    := fun x y : E => is_inv_l E sum E_0 sum_id x y; 

  sum_is_inv_r
    :  forall x y : E, Prop
    := fun (x y : E) => is_inv_r E sum E_0 sum_id x y;

  sum_is_inv
    :  forall x y : E, Prop
    := fun (x y : E) => is_inv E sum E_0 sum_id x y;

  sum_inv_l_ex : forall x : E, exists y : E, sum_is_inv_l x y;

  prod_is_assoc : is_assoc E prod;

  prod_is_comm : is_comm E prod;
  
  prod_is_id_l
    :  E -> Prop
    := fun x : E => is_id_l E prod x;

  prod_is_id_r
    :  E -> Prop
    := fun x : E => is_id_r E prod x;

  prod_is_id
    :  E -> Prop
    := fun x : E => is_id E prod x;

  prod_id_l : prod_is_id_l E_1;

  prod_id_r
    :  prod_is_id_r E_1
    := fun x : E
         =>  prod_id_l x
         =|= (fun a => a = x) by (prod_is_comm x E_1);

  prod_id
    :  prod_is_id E_1
    := conj prod_id_l prod_id_r;

  prod_is_inv_l
    :  forall x y : E, Prop
    := fun x y : E => is_inv_l E prod E_1 prod_id x y; 

  prod_is_inv_r
    :  forall x y : E, Prop
    := fun (x y : E) => is_inv_r E prod E_1 prod_id x y;

  prod_is_inv
    :  forall x y : E, Prop
    := fun (x y : E) => is_inv E prod E_1 prod_id x y;

  prod_inv_l_ex : forall x : E, exists y : E, prod_is_inv_l x y;

  prod_sum_distrib_l : is_distrib_l E prod sum;
 
  lt_sum_intro_l
    :  forall x y z : E, lt x y -> lt (sum z x) (sum z y)
    := fun x y z H
         =>  eq_refl (lt z x)
         =|= [[ y | x ]] (fun a => op z x = op z a) by H;

  is_positive
    :  forall x : E, Prop
    := fun x => lt E_0 x;

  is_negative
    :  forall x : E, Prop
    := fun x => lt x E_0;

  lt_trichotomy : forall x : E, is_negative x \/ (x = E_0 \/ is_positive x);

  lt_closure_sum : forall x y : E, is_positive x -> is_positive y -> is_positive (sum x y);

  lt_closure_prod : forall x y : E, is_positive x -> is_positive y -> is_positive (prod x y);
}.
