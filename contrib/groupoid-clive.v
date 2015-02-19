Require Import HoTT.

Record CategoryStruct {obj : hSet} {hom : obj -> obj -> hSet} : Type := {
  id : forall x : obj, hom x x;
  comp : forall {x y z : obj},
    hom y z -> hom x y -> hom x z
}.

Record IsCategory (obj : hSet) (hom : obj -> obj -> hSet) (cs : @CategoryStruct obj hom) : Type := {
  left_id : forall x y, forall f : hom x y,
    (comp cs) ((id cs) y) f = f;
  right_id : forall x y : obj, forall f : hom x y,
    (comp cs) f ((id cs) x) = f;
  assoc : forall x y z w : obj,
    forall f : hom z w, forall g : hom y z, forall h : hom x y,
    (comp cs) ((comp cs) f g) h = (comp cs) f ((comp cs) g h)
}.

Require Import Record.

(* Will need tactic issig3 and then equality on subset types *)

Lemma isprop_iscategory (O : hSet) (H : O -> O -> hSet) (CS : CategoryStruct) :
  IsHProp (IsCategory O H CS).