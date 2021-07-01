(** * Powerset weakly distributes over itself in toposes 
This file is an appendix of the PhD thesis of Alexandre Goy
untitled "On the Compositionality of Monads via Weak Distributive Laws"
(2021).
It contains formal proofs, valid in [Set]
and more generally in any topos, that: 
  1 - [Theorem eta_nearly_cartesian]
      the unit of the powerset monad is nearly cartesian
      iff the topos is degenerate
  2 - [Theorem mu_nearly_cartesian]
      the multiplication of the powerset monad is nearly cartesian
  3 - [Theorem monotone_weak_dlaw]
      the unique monotone weak distributive law from the powerset
      over itself is given by the expected Egli-Milner formula
  4 - [Theorem dlaw_degenerate]
      if there is a distributive law [PP -> PP]
      then the topos is degenerate
*)

(** *  Preliminaries *)

(** We define the powerset monad in the internal logic of a topos.
  - [P] is the action of the functor on objects (powerset).
      Note that [Prop] plays the role of the subobject classifier.
  - [im] is the action of the functor on morphisms (direct image).
  - [etaP] is the unit (singleton).
  - [muP] is the multiplication (union).
*)
Definition P X := X -> Prop.
Definition im [X] [Y] (f : X -> Y) (a : P X) (y : Y) := 
    exists (x : X), a x /\ f x = y.
Definition etaP X (x : X) (x' : X) := x = x'.
Definition muP X (t : P (P X)) (x : X) := exists (s : P X), s x /\ t s.

(** In any topos, extensionality holds. *)
Axiom ext : forall X, forall A B : P X, 
  (forall (x : X), A x <-> B x) -> A = B.

(** A few more constructs will be needed.
  - [inter] is the intersection of two subobjets.
  - [preim] is the preimage of a subobject under a morphism. *)
Definition inter [X] (A B : P X) (x : X) := A x /\ B x.
Notation "A ∩ B" := (inter A B) (at level 40).
Definition preim [X] [Y] (f : X -> Y) (s' : P Y) (x : X) := s' (f x).


(** * 1 - Unit *)

Inductive terminal := elt.
Definition Prop_into_terminal (P : Prop) := elt.
(** We define [full] to  be the maximal subobject of [Prop]. *)
Definition full (P : Prop) := True.

Lemma image_of_full_is_singleton :
    im Prop_into_terminal full = etaP terminal elt.
Proof.
apply ext. unfold im,full,etaP,Prop_into_terminal.
intro. destruct x. split ; intro.
  - reflexivity.
  - exists True. split ; trivial.
Qed.

(** The unit [etaP] is nearly cartesian 
if and only if the topos is degenerate. *)
Theorem eta_nearly_cartesian :
  (forall X Y (f : X -> Y) (s : P X) (y : Y), 
  im f s = etaP Y y ->
  exists (x : X), etaP X x = s /\ f x = y) <-> (True = False).
Proof.
split ; intros.
  - specialize (H Prop terminal Prop_into_terminal).
    pose proof H full elt image_of_full_is_singleton.
    destruct H0,H0.
    assert (etaP Prop x True <-> True) by (rewrite H0 ; intuition).
    assert (etaP Prop x False <-> True) by (rewrite H0 ; intuition).
    unfold etaP in H2,H3.
    assert (x = True) by (apply H2 ; trivial).
    assert (x = False) by (apply H3 ; trivial). rewrite H4 in H5.
    assumption.
  - exfalso. rewrite <- H. trivial.
Qed.


(** * 2 - Multiplication *)

Lemma frobenius : forall [X] [Y] f (s : P X) (s' : P Y),
    im f (s ∩ (preim f s')) = (im f s) ∩ s'.
Proof.
intros. apply ext. unfold preim,inter,im. intro y.
split ; intros ; destruct H,H,H.
  - rewrite H0 in H1. split ; try assumption.
    exists x. split ; assumption.
  - rewrite <- H1 in H0. exists x. auto.
Qed.

Lemma subset_in_union :
  forall X (t : P (P X)) (s : P X), t s -> muP X t ∩ s = s.
Proof.
intros. apply ext. unfold muP,inter. intro. split ; intro.
  - destruct H0. assumption.
  - split ; try assumption. exists s. split ; assumption.
Qed.

(** The multiplication [muP] is nearly cartesian. *)
Theorem mu_nearly_cartesian :
  forall X Y (f : X -> Y) (s : P X) (t' : P (P Y)),
  im f s = muP Y t' ->
  exists (t : P (P X)), muP X t = s /\ im (im f) t = t'.
Proof.
intros. exists (im (fun s' => s ∩ (preim f s')) t'). split ; apply ext.
  - intro. unfold muP,im. split ; intro.
    + destruct H0 as (s0,H0),H0,H1 as (s',H1),H1.
      rewrite <- H2 in H0. destruct H0. assumption.
    + assert ((im f s) (f x))
      by (unfold im ; exists x ; split ; try assumption ; reflexivity).
      rewrite H in H1. destruct H1 as (s', H1), H1.
      exists (s ∩ (preim f s')). split.
      * split ; assumption.
      * exists s'. auto.
  - intro s'. unfold im. split ; intro.
    + destruct H0 as (s0,H0),H0,H0 as (s'0,H0),H0.
      pose proof frobenius f s s'0. rewrite H2,H in H3.
      rewrite subset_in_union in H3 ; try assumption.
      unfold im in H3. rewrite <- H1, H3. assumption.
    + exists (s ∩ (preim f s')). split.
      * exists s'. auto.
      * pose proof frobenius f s s'. rewrite H in H1.
        rewrite subset_in_union in H1 ; assumption.
Qed.

(** * 3 - Monotone weak distributive law *)

Definition relation [X] [Y] (R : P(X * Y)) := { t : X * Y | R t}.
Definition proj1 [X] [Y] (R : P(X * Y)) (t : relation R) :=
    fst (proj1_sig t).
Definition proj2 [X] [Y] (R : P(X * Y)) (t : relation R) :=
    snd (proj1_sig t).
Definition Pext [X] [Y] (R : P(X * Y)) (u : P X * P Y) := 
    exists (t : P (relation R)),
    im (proj1 R) t = fst u /\ im (proj2 R) t = snd u.

Lemma pair_in_relation [X] [Y] (R : P(X * Y)) :
    forall r : relation R, R (proj1 R r, proj2 R r).
Proof.
intro. destruct r as (t,r0). destruct t.
unfold proj1,proj2. simpl. assumption.
Qed.

(** The relational extension is given by the Egli-Milner formula. *)
Proposition Egli_Milner [X] [Y] (R : P(X * Y)) : forall (u : P X * P Y),
    Pext R u <->
      ((forall x : X, (fst u) x -> exists y : Y, (snd u) y /\ R (x,y)) 
    /\ (forall y : Y, (snd u) y -> exists x : X, (fst u) x /\ R (x,y))).
Proof.
intro. destruct u as (s,s'). unfold Pext. simpl. split ; intro.
  - destruct H as (t,H),H. rewrite <- H, <- H0. unfold im. split.
    + intros. destruct H1 as (r,H1). destruct H1.
      exists (proj2 R r). split.
      * exists r. auto.
      * rewrite <- H2. apply pair_in_relation.
    + intros. destruct H1 as (r,H1). destruct H1.
      exists (proj1 R r). split.
      * exists r. auto.
      * rewrite <- H2. apply pair_in_relation.
  - destruct H. pose (fun (t0 : relation R) =>
    s (fst (proj1_sig t0)) /\ s' (snd (proj1_sig t0))) as t.
    exists t. split.
    + apply ext. intro x. split ; intro.
      * unfold im in H1. destruct H1 as (r,H1),H1. destruct r as (r0,H3).
        unfold t in H1. unfold proj1 in H2. simpl in *.
        destruct H1. rewrite H2 in H1. assumption.
      * specialize (H x H1). destruct H as (y,H),H. unfold im.
        exists (exist R (x,y) H2). unfold t. simpl.
        split ; try split ; assumption.
    + apply ext. intro y. split ; intro.
      * unfold im in H1. destruct H1 as (r,H1),H1.
        destruct r as (r0,H3). unfold t in H1.
        unfold proj2 in H2. simpl in *. destruct H1.
        rewrite H2 in H4. assumption.
      * specialize (H0 y H1). destruct H0 as (x,H0),H0.
        unfold im. exists (exist R (x,y) H2).
        unfold t. simpl. split ; try split ; assumption.
Qed.

Definition ni X (t : P X * X) := (fst t) (snd t).
Definition lambda_m X (t : P (P X)) (s : P X) := Pext (ni X) (t,s).

(** The monotone weak distributive law [lambda] expresses as follows. *)
Theorem monotone_weak_dlaw X : forall (t : P (P X)) (s : P X),
    lambda_m X t s <-> 
    (forall x : X, s x -> muP X t x) 
     /\ (forall u : (P X), t u -> exists (x : X), u x /\ s x).
Proof.
  intros. unfold lambda_m. unfold muP. split ; intro.
  - apply Egli_Milner in H. unfold fst,snd in H. destruct H. split.
    + intros. specialize (H0 x H1). destruct H0 as (s0,H0),H0.
      exists s0. split ; assumption.
    + intros. specialize (H u H1). destruct H as (x,H),H.
      exists x. split ; assumption.
  - apply Egli_Milner. unfold fst,snd. destruct H. split.
    + intro u. intro. specialize (H0 u H1).
      destruct H0 as (x,H0). exists x. destruct H0. split ; assumption.
    + intro x. intro. specialize (H x H1).
      destruct H as (u,H). exists u. destruct H. split ; assumption.
Qed.

(** * 4 - Distributive law *)

(** We prove that if there is a natural transformation 
[lambda : PP -> PP] satisyfing both unit axioms, then [True = False].
This is the formalisation of a proof by Klin and Salamanca in 
  - (1) "Iterated covariant powerset is not a monad", Theorem 2.4
itself inspired from a proof of Varacca following an idea of Plotkin
  - (2) "Distributing probability over nondeterminism", Theorem 3.2. *)

Definition subset [X] (s t : P X) := forall x : X, s x -> t x.
Notation "s ⊆ t" := (subset s t) (at level 60).
Lemma subset_inter [X] (s t t' : P X) : s ⊆ t -> s ⊆ t' -> s ⊆ t ∩ t'.
Proof. unfold subset,inter. intuition. Qed.
Lemma subset_refl [X] (s t : P X) : s = t -> s ⊆ t.
Proof. unfold subset. intros.  rewrite H in H0. assumption. Qed.
Lemma im_nonempty [X] [Y] (f : X -> Y) (s : P X) : 
    (exists (y : Y), (im f) s y) -> (exists (x : X), s x).
Proof. intro. destruct H as (y,H),H,H. exists x. assumption. Qed.

(** The functor [P] preserves preimages. *)
Proposition pres_preim [X] [Y] (f : X -> Y) :
    forall (s' : P Y) (s : P X), ((im f) s) ⊆ s' -> s ⊆ (preim f s').
Proof.
intros. unfold subset,im,preim. intros. apply H. exists x. auto. 
Qed.


(** Preliminaries: we define the operation
  [two] that builds a set out of two elements.
  In the terminology of (1) this is a "non-trivial idempotent term". *)
Definition two [X] (x : X) (y : X) (z : X) := z = x \/ z = y.

Lemma symmetry [X] : forall (x y : X), two x y = two y x.
Proof. unfold two. intros. apply ext. intuition. Qed.

Lemma idempotence [X] : forall (x : X), two x x = etaP X x.
Proof. intro. apply ext. unfold two,etaP. intuition. Qed.

Lemma im_two [X] [Y] (f : X -> Y) : forall (x y : X),
    (im f) (two x y) = two (f x) (f y).
Proof.
intros x x'. apply ext. intro y. unfold im,two. split ; intro.
  - destruct H,H,H ; rewrite <- H0, H ; intuition.
  - destruct H. + exists x. auto. + exists x'. auto.
Qed.

(** From here, the reader is encouraged to read Theorem 2.4 of 
Klin & Salamanca paper in parallel. Their words are "quoted". *)

(** "Assume, towards a contradiction,
    that there is such a distributive law." 
Using the following axioms,
we will be able to derive that True = False *)
Axiom lambda : forall X, P (P X) -> P (P X).
Axiom naturality : forall X Y (f : X -> Y) (t : P (P X)), 
      (im (im f)) (lambda X t) = lambda Y ((im (im f)) t).
Axiom unit_1 : forall X (s : P X),
    (lambda X) (etaP (P X) s) = im (etaP X) s.
Axiom unit_2 : forall X (s : P X),
    (lambda X) (im (etaP X) s) = etaP (P X) s.

(** "Consider sets:" (in a topos these are finite coproducts) *)
Inductive A := a | b | c | d.
Inductive U := u | v.

Lemma inter_two (x y z : A) : 
  ~(y = z) -> (two x y) ∩ (two x z) = etaP A x.
Proof.
intros. unfold inter,etaP,two. apply ext. intuition. exfalso. apply H.
rewrite <- H0. assumption.
Qed.

(** "And three functions defined by:" *)
Definition f x := match x with a => u | b => u | c => v | d => v end.
Definition g x := match x with a => u | b => v | c => u | d => v end.
Definition h x := match x with a => u | b => v | c => v | d => u end.

(** "Consider the element" *)
Definition t := two (two a b) (two c d).

(** "Analyse how the three naturality squares for [f], [g] and [h]
act on [t]. Recall that [im] acts on functions by taking direct images,
so in particular:" *)
Lemma Pf_ab : (im f) (two a b) = etaP U u.
Proof. rewrite im_two. simpl. apply idempotence. Qed.

Lemma Pf_cd : (im f) (two c d) = etaP U v.
Proof. rewrite im_two. simpl. apply idempotence. Qed.

Lemma Pg_ab : (im g) (two a b) = two u v.
Proof. rewrite im_two. reflexivity. Qed.

Lemma Ph_ab : (im h) (two a b) = two u v.
Proof. rewrite im_two. reflexivity. Qed.

Lemma Pg_cd : (im g) (two c d) = two u v.
Proof. rewrite im_two. reflexivity. Qed.

Lemma Ph_cd : (im h) (two c d) = two u v.
Proof. rewrite im_two. simpl. apply symmetry. Qed.

(** Additional lemmas needed in the sequel. *)
Lemma preim_g_u : preim g (etaP U u) = two a c.
Proof.
apply ext. unfold preim,two,etaP. intro.
split ; intros ; destruct x ; simpl in * ; intuition ; discriminate.
Qed.

Lemma preim_g_v : preim g (etaP U v) = two b d.
Proof.
apply ext. unfold preim,two,etaP. intro.
split ; intros ; destruct x ; simpl in * ; intuition ; discriminate.
Qed.

Lemma preim_h_u : preim h (etaP U u) = two a d.
Proof.
apply ext. unfold preim,two,etaP. intro.
split ; intros ; destruct x ; simpl in * ; intuition ; discriminate.
Qed.

Lemma preim_h_v : preim h (etaP U v) = two b c.
Proof.
apply ext. unfold preim,two,etaP. intro.
split ; intros ; destruct x ; simpl in * ; intuition ; discriminate.
Qed.

(** "By naturality and idempotence of [two] we get:" *)
Lemma PPg_t : (im (im g)) t = etaP (P U) (two u v).
Proof.
unfold t. rewrite im_two. rewrite Pg_ab,Pg_cd. apply idempotence.
Qed.

Lemma PPh_t : (im (im h)) t = etaP (P U) (two u v).
Proof.
unfold t. rewrite im_two. rewrite Ph_ab,Ph_cd. apply idempotence.
Qed.

(** "Hence, by a unit law for [lambda]
and naturality squares for [g] and [h] we obtain:"*)
Lemma PPg_lambdaA_t :
  (im (im g)) (lambda A t) = two (etaP U u) (etaP U v).
Proof.
rewrite naturality. rewrite PPg_t. rewrite unit_1. apply im_two.
Qed.

Lemma PPh_lambdaA_t :
  (im (im h)) (lambda A t) = two (etaP U u) (etaP U v).
Proof.
rewrite naturality. rewrite PPh_t. rewrite unit_1. apply im_two.
Qed.

(** "Which implies that [lambda A t] is non-empty:" *)
Lemma lambdaA_t_nonempty : exists (s : P A), lambda A t s.
Proof.
apply (im_nonempty (im g) (lambda A t)). rewrite PPg_lambdaA_t.
exists (etaP U u). unfold two. intuition.
Qed.

(** "and:" *)
Lemma Pg_s :
  forall (s : P A), lambda A t s -> (two (etaP U u) (etaP U v)) (im g s).
Proof.
intros. rewrite <- PPg_lambdaA_t. unfold im. exists s. intuition.
Qed.

Lemma Ph_s :
  forall (s : P A), lambda A t s -> (two (etaP U u) (etaP U v)) (im h s).
Proof.
intros. rewrite <- PPh_lambdaA_t. unfold im. exists s. intuition.
Qed.

(** "Now (...) applying the same reasoning to four cases we obtain:" *)

Lemma lambdaA_t : forall (s : P A), lambda A t s -> 
  ((s ⊆ two a c) \/ (s ⊆ two b d)) /\ ((s ⊆ two a d) \/ (s ⊆ two b c)).
Proof.
intros. split.
  - pose proof Pg_s s H.
    destruct H0 ; apply subset_refl in H0 ; apply pres_preim in H0.
    + rewrite preim_g_u in H0. auto.
    + rewrite preim_g_v in H0. auto.
  - pose proof Ph_s s H.
    destruct H0 ; apply subset_refl in H0 ; apply pres_preim in H0.
    + rewrite preim_h_u in H0. auto.
    + rewrite preim_h_v in H0. auto.
Qed.

(** "Distributing intersections over unions and using 
the intersection preservation property, we get: "*)
Lemma lambdaA_t_bis : forall (s : P A),
  lambda A t s -> (exists (x : A), s ⊆ etaP A x).
Proof.
intros. apply lambdaA_t in H. destruct H,H,H0.
  - exists a. rewrite <- inter_two with (y := c) (z := d) ;
    try discriminate. apply subset_inter ; assumption.
  - rewrite symmetry in H,H0. exists c.
    rewrite <- inter_two with (y := a) (z := b) ;
    try discriminate. apply subset_inter ; assumption.
  - rewrite symmetry in H,H0. exists d.
    rewrite <- inter_two with (y := a) (z := b) ;
    try discriminate. apply subset_inter ; assumption.
  - exists b.
    rewrite <- inter_two with (y := c) (z := d) ; try discriminate.
    apply subset_inter ; assumption.
Qed.

(** "Now let us come back to the function [f].
By naturality of [two] we get:" *)
Lemma PPf_t : (im (im f)) t = two (etaP U u) (etaP U v).
Proof. unfold t. rewrite im_two. rewrite Pf_ab,Pf_cd. reflexivity. Qed.

(** "Hence, by the naturality square for [f]
and by a unit law for [lambda]:" *)
Lemma PPf_lambdaA_t : im (im f) (lambda A t) = etaP (P U) (two u v).
Proof.
rewrite naturality. rewrite PPf_t. rewrite <- unit_2.
rewrite im_two. reflexivity.
Qed.

(** "This means that:" *)
Lemma Pf_expression : forall (s : P A),
  (lambda A t s) -> (im f) s = two u v.
Proof.
intros. pose proof PPf_lambdaA_t.
assert (im (im f) (lambda A t) (im f s)
<-> etaP (P U) (two u v) (im f s)) by (rewrite H0 ; intuition).
unfold etaP in H1. symmetry. apply H1. exists s. auto.
Qed.

(** "But this contradicts the assumption that [two] is nontrivial." *)
Theorem dlaw_degenerate : True = False.
Proof.
pose proof lambdaA_t_nonempty. destruct H as (s,H).
pose proof Pf_expression s H.
assert (exists x : A, s ⊆ etaP A x) by (apply lambdaA_t_bis; assumption).
destruct H1 as (x,H1).
assert (im f s u) by (rewrite H0 ; unfold two ; intuition).
assert (im f s v) by (rewrite H0 ; unfold two ; intuition).
destruct H2,H3,H2,H3. pose proof H1 x0 H2.
pose proof H1 x1 H3. rewrite H6 in H7. destruct x0,x1 ; discriminate.
Qed.