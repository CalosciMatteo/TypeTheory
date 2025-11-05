
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Unset Universe Checking.

  (* Upstream issues to possibly raise about [setquot]:
  - should [pr1] of [eqrel] coerce to [hrel], not directly to [Funclass]?
  - should [setquotfun2'] replace [setquotfun2]? [setquotfun2'] seems strictly more general and like it should behave just as well    *)

  (** Variant of [setquotuniv] with the [isaset] hypothesis separated out,
  for easier interactive use with [use], analogous to [setquotunivprop']. *)
  Definition setquotuniv' {X : UU} {R : hrel X} {Y : UU}
      (isaset_Y : isaset Y) (f : X -> Y) (f_respects_R : iscomprelfun R f)
    : setquot R -> Y.
  Proof.
    use (setquotuniv _ (_,,_)); assumption.
  Defined.

  Definition setquotuniv_isaprop {X : UU} {R : hrel X} {Y : UU}
      (isaprop_Y : isaprop Y) (f : X -> Y) : setquot R -> Y.
  Proof.
    use setquotuniv'.
    - now apply isasetaprop.
    - exact f.
    - intros x y h.
      now apply isaprop_Y.
  Defined.

  (** [setquot_rect]: the general dependent universal property of [setquot].
  To give a function into a dependent family of sets over the quotient, it suffices to construct the function on the domain of the quotient, and show your construction respects equivalence.

  Unfortunately, this currently doesn’t compute; the intended “computation” is given as a lemma, [setquot_comp.] *)
  (* TODO: with a bit more thought, could one give a version that computes nicely, like [setquotuniv]? *)
  (* TODO: possible alternative name [setquotuniv_dep] *)
  Definition setquot_rect {X:UU} {R:eqrel X}
      (P : setquot R -> UU) (isaset_P : forall xx, isaset (P xx))
      (d : forall x:X, P (setquotpr R x))
      (d_respects_R : forall (x y:X) (r : R x y),
          transportf _ (iscompsetquotpr _ _ _ r) (d x) = d y)
    : forall xx, P xx.
  Proof.
    intros xx.
    transparent assert (f : (xx -> P xx)).
    { intros x. refine (transportf _ _ (d (pr1 x))). apply setquotl0. }
    apply (pr1image f).
    apply (squash_to_prop (eqax0 (pr2 xx))).
    2: { apply prtoimage. }
    apply invproofirrelevance. intros [y Hy] [y' Hy'].
    apply subtypePath. { intro; apply isapropishinh. } simpl.
    apply (squash_to_prop Hy). { apply isaset_P. }
    clear Hy; intros [x e_xy].
    apply (squash_to_prop Hy'). { apply isaset_P. }
    clear Hy'; intros [x' e_xy'].
    destruct e_xy, e_xy'. subst f; simpl.
    assert (R_xx' : R (pr1 x) (pr1 x')).
    { apply (eqax2 (pr2 xx)); [apply x | apply x']. }
    rewrite <- (d_respects_R _ _ R_xx').
    eapply pathscomp0. 2: { apply pathsinv0, transport_f_f. }
    apply maponpaths_2, isasetsetquot.
  Defined.

  Definition setquot_rect' {X:UU} {R:eqrel X}
  (P : setquot R -> UU) (isaset_P : forall xx, isaset (P xx))
  (d : forall x:X, P (setquotpr R x))
  (d_respects_R : forall (x y:X) (p : setquotpr R x = setquotpr R y),
      transportf _ p (d x) = d y)
  : forall xx, P xx.
  Proof.
    intros xx.
    transparent assert (f : (xx -> P xx)).
    { intros x. refine (transportf _ _ (d (pr1 x))). apply setquotl0. }
    apply (pr1image f).
    apply (squash_to_prop (eqax0 (pr2 xx))).
    2: { apply prtoimage. }
    apply invproofirrelevance. intros [y Hy] [y' Hy'].
    apply subtypePath. { intro; apply isapropishinh. } simpl.
    apply (squash_to_prop Hy). { apply isaset_P. }
    clear Hy; intros [x e_xy].
    apply (squash_to_prop Hy'). { apply isaset_P. }
    clear Hy'; intros [x' e_xy'].
    destruct e_xy, e_xy'. subst f; simpl.
    assert (R_xx' : R (pr1 x) (pr1 x')).
    { apply (eqax2 (pr2 xx)); [apply x | apply x']. }
    rewrite <- (d_respects_R _ _ (iscompsetquotpr _ _ _ R_xx')).
    eapply pathscomp0. 2: { apply pathsinv0, transport_f_f. }
    apply maponpaths_2, isasetsetquot.
  Defined.

  Definition setquot_rect_comp {X:UU} {R:eqrel X}
      (P : setquot R -> UU) (isaset_P : forall xx, isaset (P xx))
      (d : forall x:X, P (setquotpr R x))
      (d_respects_R : forall (x y:X) (r : R x y),
          transportf _ (iscompsetquotpr _ _ _ r) (d x) = d y)
    : forall x, (setquot_rect P isaset_P d d_respects_R) (setquotpr R x) = d x.
  Proof.
    intros x. unfold setquot_rect; simpl.
    eapply pathscomp0. 2: { apply idpath_transportf. }
    apply maponpaths_2, isasetsetquot.
  Defined.

  Definition setquot_rect'_comp {X:UU} {R:eqrel X}
  (P : setquot R -> UU) (isaset_P : forall xx, isaset (P xx))
  (d : forall x:X, P (setquotpr R x))
  (d_respects_R : forall (x y:X) (p : setquotpr R x = setquotpr R y),
      transportf _ p (d x) = d y)
  : forall x, (setquot_rect' P isaset_P d d_respects_R) (setquotpr R x) = d x.
  Proof.
    intros x. unfold setquot_rect'; simpl.
    eapply pathscomp0. 2: { apply idpath_transportf. }
    apply maponpaths_2, isasetsetquot.
  Defined.

  Definition setquot_rect_isaprop {X:UU} {R:eqrel X}
      (P : setquot R -> UU) (isaprop_P : forall xx, isaprop (P xx))
      (d : forall x:X, P (setquotpr R x))
    : forall xx, P xx.
  Proof.
    use (setquot_rect P (λ x, isasetaprop (isaprop_P x)) d).
    intros x y r.
    apply isaprop_P.
  Defined.
  
  Opaque setquot_rect setquot_rect_comp setquot_rect_isaprop.

(** A specialised eliminator for quotients, with better computational
behaviour than [setquot_rect], but not quite an instance of the simpler
eliminators: the target type is a subquotient, whose predicate and equivalence
relation may depend on the input, but whose underlying type is independent.

So this gives, in certain circumstances, a dependent eliminator with some
computational behaviour. *)
  Definition setquot_to_dependent_subquotient {X:UU} {R:eqrel X}
      {P_pre:UU}
      (P_good : setquot R -> hsubtype P_pre)
      (P_eq : forall xx, eqrel (P_good xx))
      (d_pre : X -> P_pre)
      (d_good : forall x:X, P_good (setquotpr R x) (d_pre x))
      (d_eq : forall (x y:X) (r : R x y),
          P_eq (setquotpr R y)
               (d_pre x,, transportf (fun xx => P_good xx (d_pre x))
                                     (iscompsetquotpr _ _ _ r) (d_good x))
               (d_pre y,, d_good y))
    : forall xx, setquot (P_eq xx).
  Proof.
    intros xx.
    transparent assert (f : (xx -> setquot (P_eq xx))).
    { intros x. apply setquotpr.
      exists (d_pre (pr1 x)).
      refine (transportf (fun xx => P_good xx (d_pre _)) _ (d_good _)).
      apply setquotl0. }
    apply (pr1image f).
    apply (squash_to_prop (eqax0 (pr2 xx))).
    2: { apply prtoimage. }
    apply invproofirrelevance. intros [y Hy] [y' Hy'].
    apply subtypePath. { intro; apply isapropishinh. } simpl.
    apply (squash_to_prop Hy). { apply isasetsetquot. }
    clear Hy; intros [x e_xy].
    apply (squash_to_prop Hy'). { apply isasetsetquot. }
    clear Hy'; intros [x' e_xy'].
    destruct e_xy, e_xy'. subst f; simpl.
    apply iscompsetquotpr.
    set (e := setquotl0 R xx x'); clearbody e.
    destruct x' as [x' x1']; simpl in *. clear x1'.
    destruct e. simpl.
    assert (r : R (pr1 x) x'). { apply eqrelsymm, (pr2 x). }
    refine (eqreltrans _ _ _ _ _ _).
    2: apply (d_eq _ _ r).
    apply eqreleq, maponpaths, propproperty.
  Defined.

  Definition setquot_to_dependent_subquotient_comp {X:UU} {R:eqrel X}
      {P_pre:UU}
      (P_good : setquot R -> hsubtype P_pre)
      (P_eq : forall xx, eqrel (P_good xx))
      (d_pre : X -> P_pre)
      (d_good : forall x:X, P_good (setquotpr R x) (d_pre x))
      (d_eq : forall (x y:X) (r : R x y),
          P_eq (setquotpr R y)
               (d_pre x,, transportf (fun xx => P_good xx (d_pre x))
                                     (iscompsetquotpr _ _ _ r) (d_good x))
               (d_pre y,, d_good y))
    : forall x,
       (setquot_to_dependent_subquotient P_good P_eq
                                   d_pre d_good d_eq) (setquotpr R x)
       = setquotpr (P_eq (setquotpr _ x)) (d_pre x,, d_good x).
  Proof.
    intros x. unfold setquot_to_dependent_subquotient; simpl.
    apply maponpaths, maponpaths, propproperty.
  Defined.

  Definition representative {X:UU} {R:eqrel X} (x:setquot R) : UU
  := hfiber (setquotpr R) x.

  Definition take_representative_with_isaset
      {X:UU} {R:eqrel X} (xx:setquot R)
      {Y:UU} (H_Y : isaset Y)
      (f : representative xx -> Y) (H_f : forall xx xx', f xx = f xx')
    : Y.
  Proof.
    simple refine (setquot_rect (fun xx' => (xx' = xx -> Y)) _ _ _ xx (idpath _)).
    - intros xx'. repeat (apply impred_isaset; intros); assumption.
    - intros x e. exact (f (x,, e)).
    - intros x y r.
      eapply pathscomp0. { use transportf_fun. }
      apply funextfun; intros e. simpl.
      apply H_f.
  Defined.

  Lemma take_representative_comp
      {X:UU} {R:eqrel X} (xx : setquot R)
      {Y:UU} (H_Y : isaset Y) (f : representative xx -> Y)
      (H_f : forall x x', f x = f x') (x : representative xx) 
    : take_representative_with_isaset xx H_Y f H_f = f x.
  Proof.
    unfold take_representative_with_isaset.
    destruct x as [x e]; induction e.
    now rewrite setquot_rect_comp.
  Qed.

  Lemma take_representative_comp_canon
      {X:UU} {R:eqrel X} (x : X)
      {Y:UU} (H_Y : isaset Y) (f : representative (setquotpr R x) -> Y)
      (H_f : forall xx xx', f xx = f xx')
    : take_representative_with_isaset (setquotpr R x) H_Y f H_f = f (x,,idpath _).
  Proof.
    now rewrite (take_representative_comp _ _ _ _ (x,, idpath _)).
  Defined.
  
  Definition take_representative_with_hSet
      {X:UU} {R:eqrel X} (xx:setquot R)
      (Y:hSet)
      (f : representative xx -> Y) (H_f : forall xx xx', f xx = f xx')
    : Y.
  Proof.
    use take_representative_with_isaset; auto; apply setproperty.
  Defined.

Section toUpstream.

  Lemma isweqtransportf2 {X : Type} {Y : X → Type} (Z : ∏ x : X, Y x → Type)
    {x x' : X} {y:Y x}
    (e : x = x')
    : isweq (transportf2 Z e y).
  Proof.
    intros. induction e. unfold transportf. simpl. apply idisweq.
  Qed.

  Definition weq_transportf2 {X : Type} {Y : X → Type} (Z : ∏ x : X, Y x → Type)
    {x x' : X} {y:Y x}
    (e : x = x')
    : Z x y ≃ Z x' (transportf Y e y).
  Proof.
    use make_weq.
    - apply transportf2.
    - apply (isweqtransportf2 Z e).
  Defined.

  Lemma isweqtransportb2 {X : Type} {Y : X → Type} (Z : ∏ x : X, Y x → Type)
    {x x' : X} {y:Y x'}
    (e : x = x')
    : isweq (transportb2 Z e y).
  Proof.
    intros. induction e. unfold transportf. simpl. apply idisweq.
  Qed.

  Definition weq_transportb2 {X : Type} {Y : X → Type} (Z : ∏ x : X, Y x → Type)
    {x x' : X} {y':Y x'}
    (e : x = x')
    : Z x' y' ≃ Z x (transportb Y e y').
  Proof.
    use make_weq.
    - apply transportb2.
    - apply (isweqtransportb2 Z e).
  Defined.

  (* This lemma combine [transportf_fun] and [transportf_sec_constant] allowing to
  compute transports over families of the form [λ x : A, ∏ y : B x, C x y] *)
  Lemma transportf_fun_sec_constant {A : UU} {B: A → UU} {C : ∏ (y : A), B y → UU}
  {a1 a2 : A} (e : a1 = a2) (f : (∏ y : B a1, C a1 y))
  : transportf (λ x : A, ∏ y : B x, C x y) e f
  = λ x, invweq (weq_transportb2 C e) ((f ∘ transportb B e) x).
  Proof.
    induction e.
    cbn.
    apply funextsec.
    intro b.
    refine (!invmap_eq _ _ _ (idpath _)).
  Defined.

  Definition idpath_transportb {X : UU} (P : X -> UU) {x : X} (p : P x) :
  transportb P (idpath x) p = p.
  Proof.
    intros. apply idpath.
  Defined.

  About transportb2.

    (* (Z : ∏ x : X, Y x → Type) *)

  Lemma transportb2totransportb {X : Type} {Y Z : X → Type} {x x' : X}
  (p : x = x') (y' : Y x') (z : Z x')
  : transportb2 (λ (x:X) (_ : Y x) , Z x) p y' z
  = transportb Z p z.
  Proof.
    induction p.
    reflexivity.
  Qed.

End toUpstream.
  
    (*  [take_representative_with_isaset_dep]
      Generalization of [take_representative_with_isaset]
      so that Y can depend on [setquot R]. *)
    
    (*  The proof uses [setquot_rect']. This next local lemma contains the
      "d_respects_R" part of the proof (opaque since it is an equality in a set)*)
    Local Lemma take_representative_with_isaset_dep_respects
    {X:UU} {R:eqrel X} (xx:setquot R)
    {Y:setquot R -> UU} (H_Y : forall xx, isaset (Y xx))
    (f : representative xx -> Y xx)
    (H_f : forall x x', f x = f x')
    x y r
    : transportf
        (λ xx' : setquot R, xx' = xx → Y xx') r
        ((λ (x0 : X) (e : setquotpr R x0 = xx), transportb Y e (f (x0,, e))) x)
    = (λ (x0 : X) (e : setquotpr R x0 = xx), transportb Y e (f (x0,, e))) y.
    Proof.
      eapply pathscomp0. { use transportf_fun_sec_constant. }    
      apply funextfun; intros e.
      unfold funcomp.
      unfold transportb.
      rewrite transportf_id2.
      simpl.
      induction e.
      simpl.
      rewrite idpath_transportf. (*TODO: delete line*)
      rewrite pathsinv0inv0, pathscomp0rid.
      apply invmap_eq.
      cbn.
      apply pathsinv0.
      eapply pathscomp0. { use transportb2totransportb. }
      unfold transportb.
      apply maponpaths.
      apply H_f.
    Qed.
  
    Definition take_representative_with_isaset_dep
    {X:UU} {R:eqrel X} (xx:setquot R)
    {Y:setquot R -> UU} (H_Y : forall xx, isaset (Y xx))
    (f : representative xx -> Y xx)
    (H_f : forall x x', f x = f x')
    : Y xx.
    Proof.
    simple refine (setquot_rect' (fun xx' => (xx' = xx -> Y xx')) _ _ _ _ (idpath _)); simpl. (*TODO: check if setquot_rect' is really needed*)
    - intros xx'; apply impred_isaset; intro. apply H_Y.
    - intros x e.
      exact (transportb _ e (f (x,,e))).
    - apply (take_representative_with_isaset_dep_respects _ H_Y _ H_f).
    Defined.
    
    Lemma take_representative_with_isaset_dep_comp
      {X:UU} {R:eqrel X} (xx:setquot R)
      {Y:setquot R -> UU} (H_Y : forall xx, isaset (Y xx))
      (f : representative xx -> Y xx)
      (H_f : forall x x', f x = f x')
      (x : representative xx)
    : take_representative_with_isaset_dep xx H_Y f H_f = f x.
    Proof.
      unfold take_representative_with_isaset_dep.
      destruct x as [x e]; induction e.
      now rewrite setquot_rect'_comp.
    Qed.

  (* TODO: perhaps add [take_representative_with_isaprop], […with_hProp] also *)
