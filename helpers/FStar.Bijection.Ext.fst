module FStar.Bijection.Ext

let bijection_injective #a #b f x1 x2 =
  f.bij.left_right x1;
  f.bij.left_right x2

let bijection_right_injective #a #b f x1 x2 =
  f.bij.left_right x1;
  f.bij.left_right x2

let bijection_surjective #a #b f y =
  f.bij.right_left y
