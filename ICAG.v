(* This file is a collection of proofs and
definitions from an Introduction to Complex
Analysis and Geometry *)

Require Import group.

Structure Field : Type := field {
  E: Set;
  E_0: E;
  E_1: E;
  sum: E -> E -> E;
  prod: E -> E -> E;

  add_assoc : GROUP.is_assoc E sum;

  mult_assoc : GROUP.is_assoc E prod;

  add_id_l : GROUP.is_id_l E sum E_0;

  add_id_r : GROUP.is_id_r E sum E_0;

  add_id : GROUP.is_id E sum E_0 := conj add_id_l add_id_r;

  mult_id_l : GROUP.is_id_l E prod E_1;

  mult_id_r : GROUP.is_id_r E prod E_1;

  mult_id : GROUP.is_id E prod E_0 := conj mult_id_l mult_id_r;

  add_group 
    :  GROUP.Group
    := group E E_0 sum add_assoc add_id_l add_id_r
}.

Section field_axioms.

Parameter F : Field.

Axiom F_add_assoc : forall x y z : F.(E), F.(sum) x (F.(sum) y z) = F.(sum) (F.(sum) x y) z.
	
Axiom F_mult_assoc : forall x y z : F.(E), F.(prod) x (F.(prod) y z) = F.(prod) (F.(prod) x y) z.

Axiom F_add_id_l : forall x : F.(E), F.(sum) F.(E_0) x = x.

Axiom F_add_id_r : forall x : F.(E), F.(sum) x F.(E_0) = x.

Axiom F_mult_id_l : forall x : F.(E), F.(prod) F.(E_1) x = x.

Axiom F_add_inv_l : forall x : F.(E), exists y : F.(E), F.(sum) x y = F.(E_0).

Axiom F_add_inv_r : forall x : F.(E), exists y : F.(E), F.(sum) y x = F.(E_0).

Axiom F_distr : forall x y z : F.(E), F.(prod) (F.(sum) y z) x = F.(sum) (F.(prod) y x) (F.(prod) z x).

Definition F_0_0 : F.(sum) F.(E_0) F.(E_0) = F.(E_0) := F_add_id_r F.(E_0).

Definition F_sum_intro_l
  :  forall x y : F.(E), x = y -> forall z : F.(E), F.(sum) z x = F.(sum) z y
  := fun (x y : F.(E)) (H : x = y) z
       => eq_ind x (fun a : F.(E) => F.(sum) z x = F.(sum) z a) eq_refl y H.  

Definition F_sum_intro_r
  :  forall x y : F.(E), x = y -> forall z : F.(E), F.(sum) x z = F.(sum) y z
  := fun (x y : F.(E)) (H : x = y) z
       => eq_ind x (fun a : F.(E) => F.(sum) x z = F.(sum) a z) eq_refl y H.  

Definition F_prod_intro_l
  :  forall x y : F.(E), x = y -> forall z : F.(E), F.(prod) z x = F.(prod) z y
  := fun (x y : F.(E)) (H : x = y) z
       => eq_ind x (fun a : F.(E) => F.(prod) z x = F.(prod) z a) eq_refl y H.  

Definition F_prod_intro_r
  :  forall x y : F.(E), x = y -> forall z : F.(E), F.(prod) x z = F.(prod) y z
  := fun (x y : F.(E)) (H : x = y) z
       => eq_ind x (fun a : F.(E) => F.(prod) x z = F.(prod) a z) eq_refl y H.  
(*
Definition F_sum_elim_l
  :  forall x y z : F.(E), F.(sum) z x = F.(sum) z y -> x = y
  := fun (x y z : F.(E)) (H : F.(sum) z x = F.(sum) z y)
       => ex_ind
            (x = y)
            (fun (a : F.(E)) (H0 : F.(sum) a z = F.(E_0))
              => let H1 
                   :  F.(sum) a (F.(sum) z x) = F.(sum) a (F.(sum) z y)
                   := F_sum_intro_l (F.(sum) z x) (F.(sum) z y) H a in
                 let H2
                   :  F.(sum) (F.(sum) a z) x = F.(sum) a (F.(sum) z y)
                   := eq_ind
                        (F.(sum) a (F.(sum) z x))
                        (fun b : F.(E) => b = F.(sum) a (F.(sum) z y))
                        H1
                        (F.(sum) (F.(sum) a z) x)
                        (F_add_assoc a z x) in
                 let H3
                   :  F.(sum) (F.(sum) a z) x = F.(sum) (F.(sum) a z) y
                   := eq_ind
                        (F.(sum) a (F.(sum) z y))
                        (fun b : F.(E) => F.(sum) (F.(sum) a z) x = b)
                        H2
                        (F.(sum) (F.(sum) a z) y)
                        (F_add_assoc a z y) in
                 let H4
                   :  F.(sum) F.(E_0) x = F.(sum) F.(E_0) y
                   := eq_ind
                        (F.(sum) a z)
                        (fun b : F.(E) => F.(sum) b x = F.(sum) b y)
                        H3
                        F.(E_0)
                        (eq_ind

Definition F_x_0 : forall x : F.(E), F.(prod) F.(E_0) x = F.(E_0)
  := fun x : F.(E)
       => let H
            :  F.(prod) F.(E_0) x = F.(prod) (F.(sum) F.(E_0) F.(E_0)) x
            := eq_ind_r (fun a : F.(E) => F.(prod) F.(E_0) x = F.(prod) a x) eq_refl F_0_0 in
          let H0
            :  F.(prod) F.(E_0) x = F.(sum) (F.(prod) F.(E_0) x) (F.(prod) F.(E_0) x)
            := eq_ind_r (fun a : F.(E) => F.(prod) F.(E_0) x = a) H (F_distr x F.(E_0) F.(E_0)) in 
          let H1
            :  F.(E_0) = F.(sum) (F.(prod) F.(E_0) x) F.(E_0) 
            := ex_intro (fun (y : F.(E)) (H2 : F.(sum) (F.(prod) F.(E_0) x) y = F.(E_0))
                 => let H3
                      :  F.(sum) (F.(prod) F.(E_0) x) y = F.(sum) (F.(sum) (F.(prod) F.(E_0) x) (F.(prod) F.(E_0) x)) y
                      := F_prod_intro_r (F.(prod) F.(E_0) x) (F.(sum) (F.(prod) F.(E_0) x) (F.(prod) F.(E_0) x)) H0 y in
                    let H4
                      :  F.(sum) (f.(prod) F.(E_0) x) y = F.(sum) (F.(prod) F.(E_0) x) (F.(sum) (f.(prod) F.(E_0) x) y)
                      := eq_ind_r
                           (* (F.(sum) (F.(prod) F.(E_0) x) (F.(prod) F.(E_0) x)) *)
                           (fun a ; F.(E) => F.(sum) (F.(prod) F.(E_0) x) y = a)
                           H3
                           (F.(sum) (F.(prod) F.(E_0) x) (F.(sum) (F.(prod) F.(E_0) x) y))
                           (F_sum_assoc 
                             (F.(prod) F.(E_0) x)
                             (F.(prod) F.(E_0) x)
                             y) in
                    let H5
                      :  F.(E_0) = F.(sum) (F.(prod) F.(E_0) x) F.(E_0) 
                      := eq_ind
                           (F.(sum) (F.(prod) F.(E_0) x) y)
                           (fun a : F.(E) => a = F.(sum) (F.(prod) F.(E_0) x) a)   
                           H4
                           F.(E_0)
                           H2 in
                    eq_ind
                      (F.(sum) (F.(prod) F.(E_0) x) F.(E_0))
                      (fun a : F.(E_0) => F.(E_0) = a)
                      H5
                      (F.(prod) F.(E_0) x)
                      F_add_id_r (F.(prod) F.(E_0) x).
*)
End field_axioms.
