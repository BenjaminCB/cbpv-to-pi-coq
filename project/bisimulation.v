From Encoding Require Export pi.

Definition bisimulation (R : proc -> proc -> Prop) : Prop :=
  forall p q,
    R p q ->
    (forall l p',
        p -( l )> p' ->
        exists q',
          q -( l )> q' /\
          R p' q') /\
    (forall l q',
        q -( l )> q' ->
        exists p',
          p -( l )> p' /\
          R p' q').

CoInductive bisimilar : proc -> proc -> Prop :=
| bisim : forall p q,
    (forall l p',
        p -( l )> p' ->
        exists q',
          q -( l )> q' /\
          bisimilar p' q') ->
    (forall l q',
        q -( l )> q' ->
        exists p',
          p -( l )> p' /\
          bisimilar p' q') ->
    bisimilar p q.

Definition weak_bisimulation (R : proc -> proc -> Prop) : Prop :=
  forall p q,
    R p q ->
    (forall l p',
        p -( l )> p' ->
        exists q',
          q =( l )> q' /\
          R p' q') /\
    (forall l q',
        q -( l )> q' ->
        exists p',
          p =( l )> p' /\
          R p' q').

CoInductive weak_bisimilar : proc -> proc -> Prop :=
| weak_bisim : forall p q,
    (forall l p',
        p -( l )> p' ->
        exists q',
          q =( l )> q' /\
          weak_bisimilar p' q') ->
    (forall l q',
        q -( l )> q' ->
        exists p',
          p =( l )> p' /\
          weak_bisimilar p' q') ->
    weak_bisimilar p q.

Notation "p ~~ q" := (weak_bisimilar p q) (at level 84).
