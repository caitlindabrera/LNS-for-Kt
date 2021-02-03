


Inductive nsrule (W : Type) (sr : rlsT W) : 
    rlsT (list (W * dir)) :=
  | NSctxt : forall ps c G H d, sr ps c -> 
    nsrule sr (map (nsext G H d) ps) (nsext G H d c).

Lemma NSctxt_nil: forall (W : Type) sr G H d c, (sr [] c : Type) ->
  @nsrule W sr [] (nsext G H d c).
Proof.
  intros until 0; intros H0.
  eapply NSctxt in H0.  simpl in H0. exact H0.
Qed.

Lemma NSctxt': forall W (sr : rlsT W) ps c G H d, sr ps c ->
    nsrule sr (map (nsext G H d) ps) (G ++ (c, d) :: H).
Proof. intros. rewrite <- nsext_def. apply NSctxt. assumption. Qed.

Definition nstail {W : Type} H (d : dir) (s : W) := (s, d) :: H.
Lemma nstail_def: forall {W : Type} H d s, 
  nstail H (d : dir) (s : W) = (s, d) :: H.
Proof.  unfold nstail. reflexivity.  Qed.

Lemma nstail_ext: forall (W : Type) H d s, 
  nstail H (d : dir) (s : W) = nsext [] H d s.
Proof.  unfold nsext.  unfold nstail. reflexivity.  Qed.

Definition nslctail {W : Type} (d : dir) (s : W) := (s, d) :: [].
Lemma nslctail_def: forall {W : Type} d s, 
  nslctail (d : dir) (s : W) = (s, d) :: [].
Proof.  unfold nslctail. reflexivity.  Qed.

Lemma nslctail_ext: forall (W : Type) d s, 
  nslctail (d : dir) (s : W) = nslcext [] d s.
Proof.  unfold nslcext.  unfold nslctail. reflexivity.  Qed.

