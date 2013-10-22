Require Export Category.Core.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section internals.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition sum_morphism (s d : C + D) : Type
    := match (s, d) with
         | (inl s, inl d) => morphism C s d
         | (inr s, inr d) => morphism D s d
         | _ => Empty
       end.

  Global Arguments sum_morphism _ _ / .

  Definition sum_identity (x : C + D) : sum_morphism x x
    := match x with
         | inl x => identity x
         | inr x => identity x
       end.

  Global Arguments sum_identity _ / .

  Definition sum_compose (s d d' : C + D)
             (m1 : sum_morphism d d') (m2 : sum_morphism s d)
  : sum_morphism s d'.
  Proof.
    case s, d, d'; simpl in *;
    solve [ case m1
          | case m2
          | eapply compose; eassumption ].
  Defined.

  Global Arguments sum_compose [_ _ _] _ _ / .
End internals.

Definition sum (C D : PreCategory) : PreCategory.
Proof.
  refine (@Build_PreCategory
            (C + D)%type
            (sum_morphism C D)
            (sum_identity C D)
            (sum_compose C D)
            _
            _
            _
            _);
  abstract (
      repeat (simpl || intros [] || intro);
      auto with morphism;
      typeclasses eauto
    ).
Defined.

Module Export CategorySumNotations.
  Infix "+" := sum : category_scope.
End CategorySumNotations.