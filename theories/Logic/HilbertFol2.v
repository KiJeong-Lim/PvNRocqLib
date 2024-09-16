Require Import PnV.Prelude.Prelude.
Require Import PnV.Data.Vector.
Require Import PnV.Math.BooleanAlgebra.
Require Import PnV.Logic.BasicFol.
Require Import PnV.Logic.BasicFol2.
Require Import PnV.Logic.HilbertFol.

Import FolNotations.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.isSubsetOf.
#[local] Notation In := L.In.

Module FolHilbert.

Infix "⊢" := HilbertFol.proves : type_scope.

Section EXTRA1.

Definition inconsistent {L : language} (Gamma : ensemble (frm L)) : Prop :=
  forall p, Gamma ⊢ p.

Context {L : language}.

Lemma inconsistent_iff (Gamma : ensemble (frm L))
  : inconsistent Gamma <-> (exists p, Gamma ⊢ p /\ Gamma ⊢ Neg_frm p).
Proof.
  split.
  - intros INCONSISTENT. exists (Eqn_frm (Var_trm 0) (Var_trm 0)). split; eapply INCONSISTENT.
  - intros [p [PROVE PROVE']] q. destruct PROVE as (ps&INCL&(PF)), PROVE' as (ps'&INCL'&(PF')).
    exists (ps' ++ ps). split. done!. econs. eapply MP.
    + rewrite <- L.app_nil_l with (l := ps'). eapply MP. exact (proof_ex_falso p q). exact PF'.
    + exact PF.
Qed.

End EXTRA1.

Section HENKIN.

#[local] Infix "=~=" := is_similar_to : type_scope.

Context {L : language}.

#[local] Notation L' := (augmented_language L Henkin_constants).

#[local] Notation hatom := (ivar + Henkin_constants)%type.

#[local] Notation hsubst := (hatom -> trm L').

#[local] Existing Instance constant_symbols_sim.

#[local] Existing Instance trm_sim.

#[local] Existing Instance trms_sim.

#[local] Existing Instance frm_sim.

#[local] Existing Instance frms_sim.

Lemma Fun_eqAxm_HC_free (f : L'.(function_symbols))
  : forall c : Henkin_constants, HC_occurs_in_frm c (Fun_eqAxm f) = false.
Proof.
  enough (HACK : forall phi : trms L' _ -> trms L' _ -> frm L', forall c,
    forall phi_a_b : forall a, forall b, forall claim : HC_occurs_in_trms c a = false /\ HC_occurs_in_trms c b = false, HC_occurs_in_frm c (phi a b) = false,
    HC_occurs_in_frm c ((nat_rec (fun _ => frm L') (prod_rec (fun _ => frm L') phi (varcouples (function_arity_table L' f))) (fun n => fun q => Imp_frm (Eqn_frm (Var_trm (n + n)) (Var_trm (S (n + n)))) q) (function_arity_table L' f))) = false
  ).
  { ii. unfold Fun_eqAxm. eapply HACK. ii. now s!. }
  induction (function_arity_table L' f) as [ | n IH]; simpl; ii.
  - rewrite phi_a_b; trivial. split; trivial.
  - s!. split. split; trivial. exploit (IH (fun ts : trms L' n => fun ts' : trms L' n => phi (S_trms n (Var_trm (n + n)) ts) (S_trms n (Var_trm (S (n + n))) ts'))).
    + ii. rewrite phi_a_b; trivial.
    + intros claim. simpl. destruct (varcouples n) as [lhs rhs] eqn: H_OBS; simpl in *. eapply claim.
Qed.

Lemma Rel_eqAxm_HC_free (R : L'.(relation_symbols))
  : forall c : Henkin_constants, HC_occurs_in_frm c (Rel_eqAxm R) = false.
Proof.
  enough (HACK : forall phi : trms L' _ -> trms L' _ -> frm L', forall c,
    forall phi_a_b : forall a, forall b, forall claim : HC_occurs_in_trms c a = false /\ HC_occurs_in_trms c b = false, HC_occurs_in_frm c (phi a b) = false,
    HC_occurs_in_frm c ((nat_rec (fun _ => frm L') (prod_rec (fun _ => frm L') phi (varcouples (relation_arity_table L' R))) (fun n => fun q => Imp_frm (Eqn_frm (Var_trm (n + n)) (Var_trm (S (n + n)))) q) (relation_arity_table L' R))) = false
  ).
  { ii. unfold Rel_eqAxm. eapply HACK. ii. now s!. }
  induction (relation_arity_table L' R) as [ | n IH]; simpl; ii.
  - rewrite phi_a_b; trivial. split; trivial.
  - s!. split. split; trivial. exploit (IH (fun ts : trms L' n => fun ts' : trms L' n => phi (S_trms n (Var_trm (n + n)) ts) (S_trms n (Var_trm (S (n + n))) ts'))).
    + ii. rewrite phi_a_b; trivial.
    + intros claim. simpl. destruct (varcouples n) as [lhs rhs] eqn: H_OBS; simpl in *. eapply claim.
Qed.

Lemma twilight_Fun_eqAxm (f : L'.(function_symbols))
  : E.empty ⊢ twilight_frm (Fun_eqAxm f).
Proof.
  rewrite untwilight_frm. 2: exact (Fun_eqAxm_HC_free f). set (n := L'.(function_arity_table) f + L'.(function_arity_table) f). set (s := fun z : ivar => Var_trm (z * 2)).
  replace (subst_frm s (Fun_eqAxm f)) with (subst_frm (fun x : ivar => if le_lt_dec n x then Var_trm x else s x) (Fun_eqAxm f)).
  - eapply for_Imp_E with (p := close_from 0 n (Fun_eqAxm f)). eapply subst_frm_close_frm with (n := n) (s := s) (p := Fun_eqAxm f).
    clearbody n. clear s. induction n as [ | n IH]; simpl.
    + exists []. split. done. econs. exact (EQN_FUN f).
    + eapply for_All_I. done. exact IH.
  - eapply equiv_subst_in_frm_implies_subst_frm_same.
    ii. destruct (le_lt_dec n z) as [LE | LT]; trivial. rewrite Fun_eqAxm_free_vars in FREE. lia.
Qed.

Lemma twilight_Rel_eqAxm (R : L'.(relation_symbols))
  : E.empty ⊢ twilight_frm (Rel_eqAxm R).
Proof.
  rewrite untwilight_frm. 2: exact (Rel_eqAxm_HC_free R). set (n := L'.(relation_arity_table) R + L'.(relation_arity_table) R). set (s := fun z : ivar => Var_trm (z * 2)).
  replace (subst_frm s (Rel_eqAxm R)) with (subst_frm (fun x : ivar => if le_lt_dec n x then Var_trm x else s x) (Rel_eqAxm R)).
  - eapply for_Imp_E with (p := close_from 0 n (Rel_eqAxm R)). eapply subst_frm_close_frm with (n := n) (s := s) (p := Rel_eqAxm R).
    clearbody n. clear s. induction n as [ | n IH]; simpl.
    + exists []. split. done. econs. exact (EQN_REL R).
    + eapply for_All_I. done. exact IH.
  - eapply equiv_subst_in_frm_implies_subst_frm_same.
    ii. destruct (le_lt_dec n z) as [LE | LT]; trivial. rewrite Rel_eqAxm_free_vars in FREE. lia.
Qed.

#[local] Opaque Nat.mul Nat.div "mod".

Lemma proves_twilight (Gamma : ensemble (frm L')) (p : frm L')
  (PROVE : Gamma ⊢ p)
  : E.image twilight_frm Gamma ⊢ twilight_frm p.
Proof.
  assert (empty_proof_intro : forall q : frm L', proof [] q -> E.empty ⊢ q).
  { ii. exists []. split. intros ?. done. econstructor. eassumption. }
  destruct PROVE as (ps&INCL&(PF)).
  assert (PROVE : E.fromList ps ⊢ p).
  { exists ps. split. done. econstructor. exact PF. }
  clear PF. revert Gamma p INCL PROVE. induction ps as [ | q ps IH]; i.
  - clear INCL. destruct PROVE as (ps&INCL&(PF)).
    assert (ps_spec : forall q : frm L', ~ L.In q ps).
    { intros q q_in. done!. }
    clear INCL. eapply extend_proves with (Gamma := E.empty). done.
    clear Gamma. induction PF; i.
    + contradiction (ps_spec p (or_introl eq_refl)).
    + eapply for_Imp_E; [eapply IHPF1 | eapply IHPF2]; intros q'; specialize ps_spec with (q := q'); ss!.
    + simpl. eapply for_All_I. done. eapply IHPF. done.
    + simpl. eapply empty_proof_intro. eapply IMP1.
    + simpl. eapply empty_proof_intro. eapply IMP2.
    + simpl. eapply empty_proof_intro. eapply CP.
    + simpl. erewrite subst_hsubst_compat_in_frm. 2: ii; reflexivity.
      replace (hsubst_frm (to_hsubst (one_subst x t)) p) with (hsubst_frm (one_hsubst (inl x) t) p).
      * enough (WTS : (twilight_frm (hsubst_frm (one_hsubst (inl x) t) p)) ≡ (subst_frm (one_subst (2 * x) (twilight_trm t)) (twilight_frm p))).
        { rewrite WTS. eapply empty_proof_intro. eapply FA1. }
        eapply twilight_frm_one_hsubst.
      * eapply equiv_hsubst_in_frm_implies_hsubst_frm_same. ii. unfold one_hsubst, cons_hsubst, nil_hsubst. unfold to_hsubst. unfold one_subst, cons_subst, nil_subst.
        destruct z as [z | z].
        { destruct (eqb _ _) as [ | ] eqn: H_OBS1; destruct (eq_dec _ _) as [EQ2 | NE2]; trivial.
          - rewrite eqb_eq in H_OBS1. hinv H_OBS1.
          - rewrite eqb_neq in H_OBS1. done!.
        }
        { destruct (eqb _ _) as [ | ] eqn: H_OBS; trivial. rewrite eqb_eq in H_OBS. hinv H_OBS. }
    + simpl. eapply empty_proof_intro. eapply FA2.
      red. rewrite Nat.mul_comm. rewrite <- twilight_frm_fvs. exact NOT_FREE.
    + simpl. eapply empty_proof_intro. eapply FA3.
    + eapply proves_reflexivity.
    + eapply for_Imp_I. eapply proves_symmetry. eapply for_ByHyp. done!.
    + eapply for_Imp_I. eapply for_Imp_I. eapply proves_transitivity with (t2 := twilight_trm (Var_trm 1)); eapply for_ByHyp; done!.
    + eapply twilight_Fun_eqAxm.
    + eapply twilight_Rel_eqAxm.
  - eapply for_Imp_E with (p := twilight_frm q).
    + change (E.image twilight_frm Gamma ⊢ twilight_frm (Imp_frm q p)). eapply IH.
      * intros p' H_in. done!.
      * rewrite Deduction_theorem. eapply extend_proves with (Gamma := E.fromList (q :: ps)).
        { intros p' H_in. done!. }
        { exact PROVE. }
    + eapply for_ByHyp. rewrite E.in_image_iff. exists q. split; trivial. eapply INCL. simpl. left. trivial.
Qed.

Lemma proves_hsubstitutivity (sigma : hsubst) (Gamma : ensemble (frm L')) (p : frm L')
  (PROVE : Gamma ⊢ p)
  : E.image (hsubst_frm sigma) Gamma ⊢ hsubst_frm sigma p.
Proof.
  assert (EQ1 : E.image (hsubst_frm sigma) Gamma == E.image (subst_frm (twilight sigma)) (E.image twilight_frm Gamma)).
  { intros z. s!. split; intros [q [-> IN]].
    - exists (twilight_frm q); split.
      + eapply twilight_frm_lemma.
      + done!.
    - rewrite E.in_image_iff in IN. destruct IN as [p' [-> IN]]. exists p'. split.
      + symmetry. eapply twilight_frm_lemma.
      + done!.
  }
  rewrite EQ1. rewrite twilight_frm_lemma. eapply proves_substitutivity. eapply proves_twilight. exact PROVE.
Qed.

Lemma embed_frm_Fun_eqAxm (f : L.(function_symbols))
  : embed_frm (@Fun_eqAxm L f) = @Fun_eqAxm L' f.
Proof.
  enough (HACK : forall phi : trms L (function_arity_table L f) -> trms L (function_arity_table L f) -> frm L, forall phi' : trms L' (function_arity_table L' f) -> trms L' (function_arity_table L' f) -> frm L',
    forall INVARIANT : forall a, forall b, embed_frm (phi a b) = phi' (embed_trms a) (embed_trms b),
    embed_frm (eqns_imp (prod_rec (fun _ => frm L) phi (varcouples (function_arity_table L f))) (function_arity_table L f)) = eqns_imp (prod_rec (fun _ => frm L') phi' (varcouples (function_arity_table L f))) (function_arity_table L f)
  ).
  { unfold Fun_eqAxm. simpl. ii; eapply HACK. ii; reflexivity. }
  simpl. generalize (function_arity_table L f) as n; clear f. induction n as [ | n IH]; simpl; ii.
  - rewrite INVARIANT. reflexivity.
  - exploit (IH (fun ts => fun ts' => phi (S_trms n (Var_trm (n + n)) ts) (S_trms n (Var_trm (S (n + n))) ts')) (fun ts => fun ts' => phi' (S_trms n (Var_trm (n + n)) ts) (S_trms n (Var_trm (S (n + n))) ts'))).
    + ii. rewrite INVARIANT. reflexivity.
    + intros claim. destruct (@varcouples L n) as [lhs rhs] eqn: H_OBS, (@varcouples L' n) as [lhs' rhs'] eqn: H_OBS'; simpl. f_equal; trivial.
Qed.

Lemma embed_frm_Rel_eqAxm (R : L.(relation_symbols))
  : embed_frm (@Rel_eqAxm L R) = @Rel_eqAxm L' R.
Proof.
  enough (HACK : forall phi : trms L (relation_arity_table L R) -> trms L (relation_arity_table L R) -> frm L, forall phi' : trms L' (relation_arity_table L' R) -> trms L' (relation_arity_table L' R) -> frm L',
    forall INVARIANT : forall a, forall b, embed_frm (phi a b) = phi' (embed_trms a) (embed_trms b),
    embed_frm (eqns_imp (prod_rec (fun _ => frm L) phi (varcouples (relation_arity_table L R))) (relation_arity_table L R)) = eqns_imp (prod_rec (fun _ => frm L') phi' (varcouples (relation_arity_table L R))) (relation_arity_table L R)
  ).
  { unfold Rel_eqAxm. simpl. ii; eapply HACK. ii; reflexivity. }
  simpl. generalize (relation_arity_table L R) as n; clear R. induction n as [ | n IH]; simpl; ii.
  - rewrite INVARIANT. reflexivity.
  - exploit (IH (fun ts => fun ts' => phi (S_trms n (Var_trm (n + n)) ts) (S_trms n (Var_trm (S (n + n))) ts')) (fun ts => fun ts' => phi' (S_trms n (Var_trm (n + n)) ts) (S_trms n (Var_trm (S (n + n))) ts'))).
    + ii. rewrite INVARIANT. reflexivity.
    + intros claim. destruct (@varcouples L n) as [lhs rhs] eqn: H_OBS, (@varcouples L' n) as [lhs' rhs'] eqn: H_OBS'; simpl. f_equal; trivial.
Qed.

Lemma embed_proves (Gamma : ensemble (frm L)) (p : frm L)
  (PROVE : Gamma ⊢ p)
  : E.image embed_frm Gamma ⊢ embed_frm p.
Proof.
  assert (empty_proof_intro : forall q : frm L', proof [] q -> E.empty ⊢ q).
  { ii. exists []. split. intros ?. done. econstructor. eassumption. }
  destruct PROVE as (ps&INCL&(PF)).
  assert (PROVE : E.fromList ps ⊢ p).
  { exists ps. split. done. econstructor. exact PF. }
  clear PF. revert Gamma p INCL PROVE. induction ps as [ | q ps IH]; i.
  - clear INCL. destruct PROVE as (ps&INCL&(PF)).
    assert (ps_spec : forall q : frm L, ~ L.In q ps).
    { intros q q_in. done!. }
    clear INCL. eapply extend_proves with (Gamma := E.empty). done.
    clear Gamma. induction PF; i.
    + contradiction (ps_spec p (or_introl eq_refl)).
    + eapply for_Imp_E; [eapply IHPF1 | eapply IHPF2]; intros q'; specialize ps_spec with (q := q'); ss!.
    + simpl. eapply for_All_I. done. eapply IHPF. done.
    + simpl. eapply empty_proof_intro. eapply IMP1.
    + simpl. eapply empty_proof_intro. eapply IMP2.
    + simpl. eapply empty_proof_intro. eapply CP.
    + simpl. eapply empty_proof_intro. rewrite embed_subst_frm.
      replace (subst_frm (embed_trm ∘ one_subst x t)%prg (embed_frm p)) with (subst_frm (one_subst x (embed_trm t)) (embed_frm p)).
      * eapply FA1.
      * eapply equiv_subst_in_frm_implies_subst_frm_same. ii. unfold one_subst, cons_subst, nil_subst. unfold "∘"%prg. destruct (eq_dec z x) as [EQ1 | NE1]; trivial.
    + simpl. eapply empty_proof_intro. eapply FA2.
      red. rewrite embed_fvs_frm. exact NOT_FREE.
    + simpl. eapply empty_proof_intro. eapply FA3.
    + eapply proves_reflexivity.
    + eapply for_Imp_I. eapply proves_symmetry. eapply for_ByHyp. done!.
    + eapply for_Imp_I. eapply for_Imp_I. eapply proves_transitivity with (t2 := embed_trm (Var_trm 1)); eapply for_ByHyp; done!.
    + rewrite embed_frm_Fun_eqAxm. eapply empty_proof_intro. exact (@EQN_FUN L' f).
    + rewrite embed_frm_Rel_eqAxm. eapply empty_proof_intro. exact (@EQN_REL L' R).
  - eapply for_Imp_E with (p := embed_frm q).
    + change (E.image embed_frm Gamma ⊢ embed_frm (Imp_frm q p)). eapply IH.
      * intros p' H_in. done!.
      * rewrite Deduction_theorem. eapply extend_proves with (Gamma := E.fromList (q :: ps)).
        { intros p' H_in. done!. }
        { exact PROVE. }
    + eapply for_ByHyp. rewrite E.in_image_iff. exists q. split; trivial. eapply INCL. simpl. left. trivial.
Qed.

(* Inductive proves_sim : frm L -> frm L' -> Prop :=
  | proves_sim_atomic_has_hc p p' hc
    (ATOMIC : frm_depth p' = 0)
    (HAS_HC : occurs_free_in_frm hc p' = true)
    (TRUE : p = Eqn_frm (Var_trm 0) (Var_trm 0))
    : proves_sim p p'
  | proves_sim_atomic_hcless p p'
    (ATOMIC : frm_depth p' = 0)
    (HCLESS : forall hc, occurs_free_in_frm hc p' = false)
    (EMBED : embed_frm p = p')
    : proves_sim p p'
  | proves_sim_neg_frm p1 p1'
    (SIM1 : proves_sim p1 p1')
    : proves_sim (Neg_frm p1) (Neg_frm p1')
  | proves_sim_imp_frm p1 p2 p1' p2'
    (SIM1 : proves_sim p1 p1')
    (SIM2 : proves_sim p2 p2')
    : proves_sim (Imp_frm p1 p2) (Imp_frm p1' p2')
  | proves_sim_all_frm y p1 p1'
    (SIM1 : proves_sim p1 p1')
    : proves_sim (All_frm y p1) (All_frm y p1').

Lemma proves_sim_witness (p' : frm L')
  : exists p : frm L, proves_sim p p'.
Admitted.

Lemma proves_sim_intro (p : frm L)
  : proves_sim p (embed_frm p).
Admitted.

Lemma embed_proves_inv (Gamma : ensemble (frm L)) (p : frm L)
  (PROVE : E.image embed_frm Gamma ⊢ embed_frm p)
  : Gamma ⊢ p.
Proof.
  destruct PROVE as (ps&INCL&(PF)).
  assert (claim : exists qs : list (frm L), ps = L.map embed_frm qs).
  { clear PF p. revert Gamma INCL; induction ps as [ | p ps IH]; simpl; i.
    - exists []. reflexivity.
    - exploit (IH Gamma). done!. intros [qs ->]. exploit (INCL p). done!.
      intros IN. s!. destruct IN as [q [-> IN]]. exists (q :: qs). reflexivity.
  }
  destruct claim as [qs claim]. subst ps.
  assert (PROVE : E.fromList (L.map embed_frm qs) ⊢ embed_frm p).
  { exists (L.map embed_frm qs). split. done!. econs. exact PF. }
  clear PF. revert Gamma p INCL PROVE. induction qs as [ | q qs IH]; i.
  - clear INCL. destruct PROVE as (ps&INCL&(PF)).
    assert (ps_spec : forall q : frm L', ~ L.In q ps).
    { intros q q_in. done!. }
    clear INCL. eapply extend_proves with (Gamma := E.empty). done.
    clear Gamma. remember (embed_frm p) as p' eqn: H_p' in PF.
    assert (INVARIANT : proves_sim p p').
    { subst p'. eapply proves_sim_intro. }
    clear H_p'. revert p INVARIANT. induction PF; intros q' ?.
    + contradiction (ps_spec p (or_introl eq_refl)).
    + rename p into A, q' into B.
      assert (H1 : forall q : frm L', ~ In q ps1).
      { ii; eapply ps_spec; done!. }
      assert (H2 : forall q : frm L', ~ In q ps2).
      { ii; eapply ps_spec; done!. }
      specialize (IHPF1 H1). specialize (IHPF2 H2). clear H1 H2 ps_spec. rename B into p, q into B.
      pose proof (proves_sim_witness A) as [q WITNESS]. eapply for_Imp_E with (p := q).
      * eapply IHPF1. econs 4; trivial.
      * eapply IHPF2; trivial.
    + 
  - eapply for_Imp_E with (p := q).
    + eapply IH.
      * intros p' H_in. exploit (INCL p'). ss!. intros IN. ss!.
      * simpl. rewrite Deduction_theorem. eapply extend_proves with (Gamma := E.fromList (L.map embed_frm (q :: qs))).
        { intros p' H_in. done!. }
        { exact PROVE. }
    + eapply for_ByHyp. exploit (INCL (embed_frm q)). ss!. intros IN. ss!. apply embed_frm_inj in H; subst x; done.
Admitted.

Theorem similar_equiconsistent (Gamma : ensemble (frm L)) (Gamma' : ensemble (frm L'))
  (SIM : Gamma =~= Gamma')
  : inconsistent Gamma <-> inconsistent Gamma'.
Proof.
  split; intros INCONSISTENT.
  - rewrite inconsistent_iff in INCONSISTENT. rewrite inconsistent_iff.
    destruct INCONSISTENT as [p [PROVE PROVE']]. exists (embed_frm p).
    rewrite <- embed_frms_spec in SIM. rewrite <- SIM. split.
    + eapply embed_proves; trivial.
    + change (E.image embed_frm Gamma ⊢ embed_frm (Neg_frm p)). eapply embed_proves; trivial.
  - admit. (* rewrite <- embed_frms_spec in SIM. intros p. pose proof (INCONSISTENT (embed_frm p)) as PROVE.
    rewrite <- SIM in PROVE. destruct PROVE as (ps&INCL&(PF)).
    remember (embed_frm p) as p' eqn: H_p' in PF. symmetry in H_p'. rewrite embed_frm_spec in H_p'. rename p into A. revert A H_p'. induction PF; i.
    + eapply for_ByHyp. rewrite <- embed_frm_spec in H_p'. subst p. exploit (INCL (embed_frm A)). done!.
      intros IN. s!. destruct IN as [p [EQ IN]]. apply embed_frm_inj in EQ. subst p. exact IN.
    + rewrite <- embed_frm_spec in H_p'. subst q. rename p into p', A into p.
      pose proof (INCONSISTENT (embed_frm p)) as PROVE. *)
Admitted. *)

End HENKIN.

End FolHilbert.
