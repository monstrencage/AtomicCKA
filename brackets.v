Require Import tools Bool.

Inductive brack := Open | Close.

Global Instance dec_brack : decidable_set brack.
Proof.
  set (brack_eqX := fun a b => match a,b with Open,Open | Close,Close => true
                                      | _,_ => false end).
  apply (@Build_decidable_set _ brack_eqX).
  intros [] [];simpl;apply ReflectT||apply ReflectF;firstorder discriminate.
Qed.
