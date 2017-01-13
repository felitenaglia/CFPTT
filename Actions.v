(*******************************************************************
 * Este archivo especifica las acciones
 * (Como transformadores de estado)
 ******************************************************************)

Section Actions.

Require Export State.

(* Ejercicio 7.2 *)
(* Accion. Se definen solo las 3 acciones pedidas *)
Inductive action : Set :=
           read : vadd -> action
         | write : vadd -> value -> action
         | chmod : action.

(* Ejercicio 7.3 *)
Variable ctx : context.

Definition va_mapped_to_ma (s:state) (va:vadd) (ma:madd) : Prop :=
           exists os_inf : os_info, oss s (active_os s) = Some os_inf /\ 
             exists p_m : padd -> option madd, hypervisor s (active_os s) = Some p_m /\
               exists mdir : madd, p_m (curr_page os_inf) = Some mdir /\
                 exists pg : page, memory s mdir = Some pg /\
                   exists v_m : vadd -> option madd, page_content pg = PT v_m /\ v_m va = Some ma.
            
Definition is_RW (o : option page) :=
               exists p v, o = Some p /\ page_content p = RW v.

Definition Pre_read (s:state) (va:vadd) : Prop := 
                ctxt_vadd_accessible ctx va  = true
             /\ aos_activity s = running
             /\ (exists ma : madd, 
                      va_mapped_to_ma s va ma
                   /\ is_RW (memory s ma)).

Definition Post_read (s:state) (va:vadd) (s':state) : Prop := s = s'.

Definition Pre_write (s:state) (va:vadd) (val:value) : Prop := 
                ctxt_vadd_accessible ctx va  = true
             /\ aos_activity s = running
             /\ (exists ma : madd,
                      va_mapped_to_ma s va ma
                   /\ is_RW (memory s ma)).

Definition Post_write (s:state) (va:vadd) (val:value) (s':state) : Prop := 
                exists ma : madd, va_mapped_to_ma s va ma
                  /\ (forall md : madd,
                              (md <> ma -> memory s' md = memory s md)
                           /\ (md = ma -> memory s' md = Some (Page (RW (Some val)) (Os (active_os s)))))
                  /\ active_os s' = active_os s
                  /\ aos_exec_mode s' = aos_exec_mode s
                  /\ aos_activity s' = aos_activity s
                  /\ oss s' = oss s
                  /\ hypervisor s' = hypervisor s.

Definition Pre_chmod (s:state) : Prop :=
                 aos_activity s = waiting 
              /\ exists os_inf : os_info, oss s (active_os s) = Some os_inf /\ hcall os_inf = None.

Definition Post_chmod (s:state) (s':state) : Prop :=
                 ((ctxt_oss ctx (active_os s) = true /\ aos_exec_mode s' = svc /\ aos_activity s' = running)
                   \/ (ctxt_oss ctx (active_os s) = false /\ aos_exec_mode s' = usr /\ aos_activity s' = running))
                 /\ active_os s' = active_os s
                 /\ oss s' = oss s
                 /\ hypervisor s' = hypervisor s
                 /\ memory s' = memory s.

Definition Pre (s:state) (a:action) : Prop :=
         match a with
          | read va => Pre_read s va
          | write va val => Pre_write s va val
          | chmod => Pre_chmod s
         end.

Definition Post (s:state) (a:action) (s':state) : Prop :=
         match a with
          | read va => Post_read s va s'
          | write va val => Post_write s va val s'
          | chmod => Post_chmod s s'
         end.

(* Ejercicio 7.5*)         
Definition PropIII (s:state) : Prop := 
                    (aos_activity s = running /\ ctxt_oss ctx (active_os s) = true)
                  \/ aos_activity s = waiting (* Esta ejecutando el hypervisor *)
                     -> aos_exec_mode s = svc.
         
Definition PropV_mapping (s:state) : Prop := 
               forall osi : os_ident, forall p_m : padd -> option madd, forall pa : padd,
                 hypervisor s osi = Some p_m ->
                   exists ma:madd, p_m pa = Some ma /\
                   exists pg:page, memory s ma = Some pg /\ page_owned_by pg = Os osi.
                  

Definition PropV_inyectividad (s:state) : Prop :=
               forall osi : os_ident, forall p_m : padd -> option madd,
                  hypervisor s osi = Some p_m ->
                     forall p1 p2 : padd, p1 <> p2 -> p_m p1 <> p_m p2 \/ p_m p1 = None.

Definition PropV (s:state) : Prop := PropV_mapping s /\ PropV_inyectividad s.

Definition PropVI (s:state) : Prop := 
               forall osi : os_ident, forall ma1 ma2 : madd, forall pg1 : page, 
               forall v_m : vadd -> option madd, forall va : vadd, 
                   memory s ma1 = Some pg1 ->
                   page_content pg1 = PT v_m ->
                   page_owned_by pg1 = Os osi ->
                   v_m va = Some ma2 ->
                   exists pg2:page,
                        memory s ma2 = Some pg2
                       /\ (ctxt_vadd_accessible ctx va = true -> page_owned_by pg2 = Os osi)
                       /\ (ctxt_vadd_accessible ctx va = false -> page_owned_by pg2 = Hyp).

(* Se define valid_state solo con las 3 propiedades pedidas *)
Definition valid_state (s:state) := PropIII s /\ PropV s /\ PropVI s.

(* Ejercicio 7.4 *)

Inductive one_step_exec (s:state) (a:action) (s':state) : Prop := 
                 ose : valid_state s -> Pre s a -> Post s a s' -> one_step_exec s a s'.
                      
(* Ejercicio 7.6 *)
Lemma ej7_6 : forall s s':state, forall a:action, Pre s a -> Post s a s'-> PropIII s -> PropIII s'.
Proof.
  intros.
  unfold PropIII.
  intro.
  case_eq a ; intros.
    (* Caso read *)
    rewrite -> H3 in *.
    simpl in H0.
    unfold Post_read in H0.
    unfold PropIII in H1.
    rewrite -> H0 in H1.
    apply (H1 H2).
    (* Caso write *)
    rewrite -> H3 in *.
    simpl in H0.
    unfold Post_write in H0.
    unfold PropIII in H1.
    elim H0; clear H0; intros.
    elim H0; clear H0; intros.
    elim H4; clear H4; intros.
    elim H5; clear H5; intros.
    elim H6; clear H6; intros.
    elim H7; clear H7; intros.
    rewrite -> H6.
    rewrite -> H7 in H2.
    rewrite -> H5 in H2.
    apply (H1 H2).
    (* Caso chmod *)
    rewrite -> H3 in *.
    simpl in H0.
    unfold Post_chmod in H0.
    elim H0; clear H0; intros.
    elim H0; intros. 
      (* Caso SO confiable *)
      apply H5.
      (* Caso SO no confiable *)
      elim H5; clear H5; intros.
      elim H6; clear H6; intros.
      elim H2; intros.
        (* Caso SO confiable *)
        elim H8; clear H8; intros.
        elim H4; clear H4; intros.
        rewrite H4 in H9.
        rewrite -> H9 in H5.
        inversion H5.
        (* Caso Hypervisor *)
        rewrite H7 in H8.
        inversion H8.
Qed.

(* Ejercicio 7.7 *)
Lemma read_isolation : forall s s':state, forall va:vadd,
                       one_step_exec s (read va) s' ->
                              exists ma:madd, va_mapped_to_ma s va ma /\
                              exists pg: page, Some pg = memory s ma /\ page_owned_by pg = Os (active_os s).
Proof.
  intros.
  elim H; clear H; intros.
  simpl in H0.
  unfold Pre_read in H0.
  elim H0; clear H0; intros.
  elim H2; clear H2; intros.
  elim H3; clear H3; intros.
  exists x.
  split; try apply H3.
  unfold valid_state in H.
  elim H; clear H; intros p3 H.
  elim H; clear H; intros p5 p6.
  elim H3; clear H3; intros.

  (* Las sucesivas aplicaciones de la táctica 
     'elim' son para sacar todas las instancias
     de los existenciales en H : va_mapped_to_ma s va x *)
  elim H; clear H; intros osi H.
  elim H; clear H; intros.
  elim H4; clear H4; intros p_m H4.
  elim H4; clear H4; intros.
  elim H5; clear H5; intros mdir H5.
  elim H5; clear H5; intros.
  elim H6; clear H6; intros pg H6.
  elim H6; clear H6; intros.
  elim H7; clear H7; intros v_m H7.
  elim H7; clear H7; intros.

  unfold PropVI in p6.
  elim (p6 (active_os s) mdir x pg v_m va H6 H7); try auto.
    (* Termino de probar el goal principal *)
    intros.
    exists x0.
    elim H9; clear H9; intros.
    elim H10; clear H10; intros.
    split; auto.
    (* Pruebo uno de las hipotesis necesarias de la propiedad 6 *)
    unfold PropV in p5.
    elim p5; clear p5; intros p5 p5_iny.
    unfold PropV_mapping in p5.
    elim (p5 (active_os s) p_m (curr_page osi) H4) ; intros.
    elim H9; clear H9; intros.
    elim H10; clear H10; intros.
    elim H10; clear H10; intros.
    rewrite -> H5 in H9.
    injection H9; intro.
    rewrite <- H12 in H10.
    rewrite -> H6 in H10.
    injection H10; intro.
    rewrite H13.
    auto.
Qed.

End Actions.
