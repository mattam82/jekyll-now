Require Import HoTT.
Require Import HoTT.Types.Bool.
Set Universe Polymorphism.

Section UniqueEx.
  Context `{Funext}.

  (** Unique existence of an [x : A] such that [P x]:
      there exists an A and it is the only one w.r.t equality *)

  Definition exists_unique {A : Type} (P : A -> Type) :=
    { x : A & (P x * forall y : A, P y -> x = y) }.

  (** Unique existence is clearly an HProp: by construction only
      one witness exists, as long as the predicate is an HProp itself. *)

  Lemma exists_unique_hprop {A} `{IsHSet A} {P : A -> hProp} : IsHProp (exists_unique P).
  Proof.
    unfold exists_unique.
    refine (ishprop_sigma_disjoint (A:=A) _).
    intros x y [px pxy] [py _].
    exact (pxy y py).
  Defined.
End UniqueEx.

Section Markov.
  Context `{Funext}.
  Universe i.
  Context (P : nat -> Bool@{i}).

  (** Regular existence *)

  Definition exP := {n : nat & P n = true}.

  (** Unique existence of a mininal such [n] with [P n = true] *)

  Definition exuP := exists_unique (fun n : nat => (P n = true) * forall k, P k = true -> n <= k).

  Instance exuP_hprop : IsHProp exuP.
  Proof.
    refine exists_unique_hprop.
  Defined.

  (** We actually have to deal with two notions of accessibility:
      The first is "indefinite" existence of a natural number satisfying
      [P]. In vanila Coq with Prop, this can be used directly to prove termination
      of a function of type [(exists n : nat, P n) -> { n : nat | P n }],
      using the idea that accessibility is a proposition.
   *)

  Inductive acc_some_nat (i : nat) : Type :=
    AccNat_true : P i = true -> acc_some_nat i
  | AccNat_succ : acc_some_nat (S i) -> acc_some_nat i.

  (** The second one is accessibility only of the initial segment of
      natural numbers up to the one for which [P] holds.

      While [acc_some_nat i] type is not an [HProp] in general as there
      may be multiple [P i = true] proofs in general, [acc_nat] is. *)

  Inductive acc_nat (i : nat) : Type :=
    AccNat0 : P i = true -> acc_nat i
  | AccNatS : P i = false -> acc_nat (S i) -> acc_nat i.

  (** We show that [acc_nat n] for any [n] is an [HProp].
      This relies on the fact that [bool] is an [HSet]. *)

  Instance acc_nat_hprop n : IsHProp (acc_nat n).
  Proof.
    apply equiv_hprop_allpath.
    intros x y.
    induction x; destruct y.
    destruct (set_path2 p p0). apply idpath.
    elimtype Empty. rewrite p in p0.
    now apply true_ne_false.

    elimtype Empty; rewrite p in p0.
    now apply true_ne_false; symmetry.

    destruct (set_path2 p p0).
    destruct (IHx y).
    apply idpath.
  Defined.

  Ltac easy ::= trivial || assumption.

  (** For [acc_some_nat n], if some [P (x + n) = true] proof exists,
      then [n] is accessible. This follows the same pattern as the
      usual Coq proof with [acc_some_nat] in [Prop]. *)

  Lemma acc_some_nat_plus : forall x n : nat,
      P (x + n) = true ->
      acc_some_nat n.
  Proof.
    induction x; intros; simpl in X.
    - now constructor.
    - constructor 2. apply IHx. now rewrite <- nat_plus_n_Sm.
  Defined.

  (** So assuming (non-unique) existence, [0] is accessible. *)

  Lemma acc_some_nat_0 : exP -> acc_some_nat 0.
  Proof.
    intros Htr.
    apply (acc_some_nat_plus Htr.1). rewrite <- nat_plus_n_O.
    exact Htr.2.
  Defined.

  (** For the proof-irrelevant [acc_nat] it is a bit more involved.
      As long as [P] holds for some _minimal_ [x + n], [acc_nat n] holds. *)

  (** We add an axiom to not do the trivial but cumbersome arithmetic proofs. *)
  Axiom arith : forall A, A.

  Lemma acc_nat_plus : forall x n : nat,
      P (x + n) = true ->
      (forall k, k < x + n -> P k = false) ->
      acc_nat n.
  Proof.
    induction x; intros; simpl in X.
    - now constructor.
    - constructor 2. apply X0. simpl.
      apply arith. (* n < (x + n).+1 *)
      apply IHx. now rewrite <- nat_plus_n_Sm.
      intros. apply X0. simpl. now rewrite nat_plus_n_Sm.
  Defined.

  (* Missing arithmetic *)

  Lemma le_Sn_m n m : n.+1 <= m -> n <= m - 1.
  Proof.
    apply arith.
  Defined.

  Lemma minus_n_0 n : n - 0 = n.
  Proof. destruct n; auto. Defined.

  Lemma gt_0_minus_1_plus_1 k m : k < m -> (m - 1).+1 = m.
  Proof.
    induction m; simpl; intros; trivial. elim H0.
    now rewrite minus_n_0.
  Defined.

  Lemma lt_Sn_m k m n : k < m -> m < n.+1 -> m - 1 < n.
  Proof.
    intros. unfold Nat.lt in *.
    change (@trunctype_type _ (dhprop_hprop (m <= n))) in X0.
    rewrite (gt_0_minus_1_plus_1 k); auto.
  Defined.

  Lemma le_not_lt n m : n <= m -> m < n -> Empty.
  Proof.
    revert m ; induction n. simpl. auto.
    intros.
    eapply IHn.
    now apply le_Sn_m; apply X.
    now apply (lt_Sn_m n).
  Defined.

  Lemma le_ne_lt m n : m <= n -> m <> n -> m < n.
  Proof.
    revert m; induction n; intros m.
    simpl in *. intros.
    elim X0. destruct m. auto. elim X.
    destruct m. trivial.
    intros. change (@trunctype_type _ (dhprop_hprop (m < n))).
    apply IHn. apply X.
    intros eqmn. rewrite eqmn in X0. elim X0. reflexivity.
  Defined.

  (** Thanks to unique existence and the fact that [acc_nat i] is an
      HProp, we can use the weaker truncated unique existence assumption
      to prove that [acc_nat 0] is inhabited.
      The proof starts by striping the truncation and applying
      [acc_nat_plus].
   *)

  Lemma acc_nat_0 : Trunc -1 exuP -> acc_nat 0.
  Proof.
    intros Htr.
    strip_truncations.
    apply (acc_nat_plus Htr.1). rewrite <- nat_plus_n_O.
    exact (fst (fst Htr.2)).

    intros.
    destruct Htr as [n [[Pn Pnbelow] Hpn]].
    simpl in X. rewrite <- nat_plus_n_O in X.
    generalize (idpath : P k = P k).
    destruct (P k) at 2 3; intros Pk.
    specialize (Pnbelow _ Pk). apply arith. (* arithmetic contradiction *)
    constructor.
  Defined.

  (** Using any of these two accessibility predicates, we can show
      untrucated existence. We can even enrich our search procedure to
      show it produces the right witness: the first natural greater or
      equal to [n] having the property [P]. *)

  Lemma acc_nat_plus_inv : forall n : nat,
      acc_nat n ->
      (exists x, (P (x + n) = true) * (forall k, n <= k -> k < n + x -> P k = false)).
  Proof.
    induction 1.
    - exists 0. split; auto. intros.
      rewrite <- nat_plus_n_O in X0. unfold Nat.lt in X0.
      apply le_not_lt in X. elim X.
      apply X0.

    - destruct IHX as [x [PSx Pfalse]].
      exists (S x); split; auto.
      + simpl. now rewrite nat_plus_n_Sm.
      + intros k ik kix.
        destruct (dec_paths i k).
        ++ now rewrite p0 in p.
        ++ assert(i < k) by apply (le_ne_lt _ _ ik n).
           apply Pfalse.
           apply X0.
           simpl. now rewrite nat_plus_n_Sm.
  Defined.

  (** A simpler version of the proof just building the witness is: *)

  Fixpoint find_ex (n : nat) (a : acc_nat n) : exP :=
    match a with
    | AccNat0 p => (n ; p)
    | AccNatS p pr => find_ex (n.+1) pr
    end.

  Lemma find_ex_wit n (p : acc_nat n) : (find_ex n p).1 = (n + (acc_nat_plus_inv n p).1)%nat.
  Proof.
    induction p; simpl. apply nat_plus_n_O.

    rewrite IHp. simpl.
    now rewrite <- nat_plus_n_Sm.
  Defined.

  (** Using the [acc_some_nat] variant, we have to be careful to
      mimick the same computational content:
      we don't use the induction hypothesis directly in the
      inductive case, but only if [P i] does not hold. *)

  Lemma find_some_ex : forall n : nat, acc_some_nat n -> exP.
  Proof.
    induction 1.
    - (* Base case *) exists i. exact p.
    - (* Inductively, we first test if [P i] holds already *)
      generalize (idpath : P i = P i).
      destruct (P i) at 2. exists i. exact X0.
      intros. exact IHX.
  Defined.

  (** We start the search at [0], using the existence or truncated
      unique existence proofs. *)

  Definition find_some_first (x : exP) := find_some_ex 0 (acc_some_nat_0 x).

  Definition find_first (t : Trunc -1 exuP) := find_ex 0 (acc_nat_0 t).

  (** Actually, there is an embedding of the accessibility proofs. *)

  Lemma acc_some_nat_acc_nat {i} : acc_some_nat i -> acc_nat i.
  Proof.
    induction 1. constructor; auto.
    generalize (idpath : P i = P i).
    destruct (P i) at 2. intros. constructor. auto.
    intros. now constructor 2.
  Defined.

  Lemma acc_nat_acc_some_nat {i} : acc_nat i -> acc_some_nat i.
  Proof.
    induction 1. constructor; auto.
    constructor 2. apply IHX.
  Defined.

  (** Finding the witness is clearly independent of the accessibility proof. *)

  Lemma find_ex_find_some_ex n (p : acc_nat n) :
    find_ex n p = find_some_ex n (acc_nat_acc_some_nat p).
  Proof.
    induction p. simpl; apply idpath.
    simpl. rewrite <- IHp.
    generalize (idpath (P i)).
    destruct (P i) at 2 3.
    intros Htrue. elimtype Empty.
    now rewrite Htrue in p; apply true_ne_false.
    intros. reflexivity.
  Defined.

  (** The following lemma is a proof that the search procedure
      [find_some_first] indeed stops at the first [i] such that [P i]
      holds, whatever the accessibility proof. *)

  Lemma find_some_ex_irrel n (x y : acc_some_nat n) : find_some_ex n x = find_some_ex n y.
  Proof.
    induction x; destruct y; simpl. now destruct (set_path2 p p0).
    generalize (idpath (P i)).
    destruct (P i) at 2 3. intros. now destruct (set_path2 p p0). intros.
    rewrite p in p0. now elimtype Empty; apply true_ne_false.
    
    generalize (idpath (P i)).
    destruct (P i) at 2 3. intros. now destruct (set_path2 p p0).
    intros; elimtype Empty. rewrite p in p0; now apply true_ne_false.

    generalize (idpath (P i)).
    destruct (P i) at 2 3 7. intros. reflexivity.
    intros. apply IHx.
  Defined.

  (** This implies that starting from an arbitrary accessibility proof
      is the same as starting from a minimal one. *)

  Lemma find_some_ex_find_ex n (p : acc_some_nat n) :
    find_some_ex n p = find_ex n (acc_some_nat_acc_nat p).
  Proof.
    rewrite find_ex_find_some_ex.
    apply find_some_ex_irrel.
  Defined.

  (** Existence of an [n] such that [P n] implies unique existence
      of a minimal [k] such that [P k].

      This uses the [find_some_first] procedure and its equivalence
      with the [find_first] procedure to show the invariant that
      the minimal [k] starting from [0] is found. *)

  Lemma exP_implies_exuP : exP -> exuP.
  Proof.
    intros x.
    generalize (idpath (find_some_first x)).
    generalize (find_some_first x) at 2.
    unfold find_some_first.
    rewrite find_some_ex_find_ex.
    intros e. intros eq.
    refine (e.1 ; ((e.2, _), _)).
    intros.
    rewrite <- eq.
    rewrite find_ex_wit. simpl.
    destruct acc_nat_plus_inv as [wit [Pwit Ptop]].
    simpl. rewrite <- nat_plus_n_O in Pwit.
    destruct (dec_paths wit k). rewrite p. apply leq_refl.
    apply arith. (* Arithmetic comparisons, getting tiring now *)

    intros.
    revert eq.
    intro. destruct eq. rewrite find_ex_wit. simpl.
    destruct acc_nat_plus_inv as [wit [Pwit Ptop]].
    simpl.
    simpl in *. rewrite <- nat_plus_n_O in Pwit.
    destruct X.
    specialize (snd _ Pwit).
    specialize (Ptop y tt).
    apply arith. (* Arithmetic getting tiring *)
  Defined.

  Import TrM.Os_ReflectiveSubuniverses.
  Import TrM.RSU.

  (** Finally, this variant of Markov's principle holds for
      propositional truncation.  We apply [find_first] under the
      propositional truncation modality. *)

  Theorem markov : Trunc -1 exP -> exP.
  Proof.
    intros.
    apply find_first.
    refine (O_functor _ exP_implies_exuP X).
  Defined.

  (** Informally, a truncated existence proof of a natural number holding for
      some _decidable_ predicate holds enough information to reconstruct
      the proof: we can use the truncated proof to guarantee the termination
      of a recursive search procedure enumerating all naturals until it
      stops at the first witness. *)

End Markov.

Print Assumptions markov.

(*
Axioms:
  istrunc_truncation : forall (n : trunc_index) (A : Type), IsTrunc n (Trunc n A)
  isequiv_apD10 : Funext -> forall (A : Type) (P : A -> Type)
     (f g : forall x : A, P x), IsEquiv apD10
  arith : forall A : Type, A
  Funext : Type0
*)

Check (@markov : Funext -> forall P : nat -> Bool, Trunc -1 (exP P) -> exP P).
