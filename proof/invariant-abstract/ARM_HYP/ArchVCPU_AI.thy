(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchVCPU_AI
imports AInvs.ArchDetSchedSchedule_AI
begin

(* FIXME MOVE *)
lemma is_tcb_TCB[simp]:
  "\<And>x.   is_tcb (TCB x)"
  "\<And>x y. \<not>is_tcb (CNode x y)"
  "\<And>x.   \<not>is_tcb (Endpoint x)"
  "\<And>x.   \<not>is_tcb (Notification x)"
  "\<And>x.   \<not>is_tcb (ArchObj x)"
 by (simp add: is_tcb_def)+

context Arch begin global_naming ARM_A

text \<open>
 The @{term arch_vcpu_tcb_valid} invariant ensures that the
 VCPU object reference in the current thread is always the
 same as the VCPU referenced by the global state.
 For global state @{term s}, the VCPU reference is obtain with
 @{term "ARM_A.arm_current_vcpu (arch_state s)"} and is of type
 @{typ "(obj_ref \<times> bool) option"}.
 The bool indicates whether the VCPU is active.
 When False, the current thread must have no VCPU reference.
 Otherwise, the global VCPU reference must equal the one in the
 current thread.
\<close>

definition
  "cur_vcpu_to_tcb_vcpu cur_vcpu =
    (case cur_vcpu of
       Some (vcpu, True) \<Rightarrow> Some vcpu
    | _ \<Rightarrow> None)"

definition
  arch_vcpu_tcb_valid_obj :: "arch_state \<Rightarrow> kernel_object \<Rightarrow> bool" where
  "arch_vcpu_tcb_valid_obj as obj \<equiv>
     \<forall>t. obj = TCB t \<longrightarrow>
           ARM_A.tcb_vcpu (tcb_arch t) = cur_vcpu_to_tcb_vcpu (ARM_A.arm_current_vcpu as)"

definition
  arch_vcpu_tcb_valid :: "'z::state_ext state \<Rightarrow> bool" where
  "arch_vcpu_tcb_valid s \<equiv>
    obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) (cur_thread s) s"

text \<open>
{@term "valid_arch_idle"} should be included in @{term invs} (global abstract spec invariant).
\<close>
definition
 valid_arch_idle :: "'z::state_ext state \<Rightarrow> bool" where
 "valid_arch_idle s \<equiv>
    obj_at (\<lambda>obj. \<forall>t. obj = TCB t \<longrightarrow> ARM_A.tcb_vcpu (tcb_arch t) = None) (idle_thread s) s"

lemmas arch_vcpu_tcb_valid_kheap_unfold =
         arch_vcpu_tcb_valid_def
         arch_vcpu_tcb_valid_obj_def
         obj_at_def
         get_tcb_ko_at

lemma arch_vcpu_tcb_valid_trans_st[simp]:
 "arch_vcpu_tcb_valid (trans_state f s) = arch_vcpu_tcb_valid s"
 "arch_vcpu_tcb_valid (trans_state f s\<lparr>cur_thread := cur\<rparr>) = arch_vcpu_tcb_valid (s\<lparr>cur_thread := cur\<rparr>)"
 " arch_vcpu_tcb_valid (trans_state f s\<lparr>is_original_cap := (is_original_cap s)(dest := x)\<rparr>) =
       arch_vcpu_tcb_valid (s\<lparr>is_original_cap := (is_original_cap s)(dest := x)\<rparr>)"
 "arch_vcpu_tcb_valid (trans_state f s\<lparr>kheap := k\<rparr>) = arch_vcpu_tcb_valid (s\<lparr>kheap := k\<rparr>)"
 by (simp add: trans_state_def arch_vcpu_tcb_valid_def obj_at_def cur_tcb_def)+

definition
 "cur_thread_tcb_vcpu s \<equiv> ARM_A.tcb_vcpu (tcb_arch (the (get_tcb (cur_thread s) s)))"

lemma arch_vcpu_tcb_validE:
  "\<lbrakk> arch_vcpu_tcb_valid s ;
     ARM_A.arm_current_vcpu (arch_state s) = ARM_A.arm_current_vcpu (arch_state t) ;
     cur_thread_tcb_vcpu s = cur_thread_tcb_vcpu t;
     tcb_at (cur_thread s) s;
     tcb_at (cur_thread t) t \<rbrakk>
   \<Longrightarrow> arch_vcpu_tcb_valid t"
  apply (clarsimp simp: arch_vcpu_tcb_valid_def tcb_at_def )
  apply (clarsimp simp: arch_vcpu_tcb_valid_obj_def obj_at_def get_tcb_ko_at cur_thread_tcb_vcpu_def)
 done

lemma lift_arch_vcpu_tcb_valid:
  "\<lbrakk> \<And>P. \<lbrace>\<lambda>s. P (cur_thread_tcb_vcpu s) \<rbrace> f \<lbrace>\<lambda>_ s. P (cur_thread_tcb_vcpu s) \<rbrace> ;
     \<And>Q. \<lbrace>\<lambda>s. Q (arch_state s) \<rbrace> f \<lbrace>\<lambda>_ s.  Q (arch_state s)\<rbrace>;
     \<lbrace>\<lambda>s. tcb_at (cur_thread s) s \<rbrace> f \<lbrace>\<lambda>_ s.  tcb_at (cur_thread s) s \<rbrace> \<rbrakk>
 \<Longrightarrow> \<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s \<rbrace> f \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s\<rbrace>"
  apply (unfold valid_def)
  apply clarsimp
  apply (erule arch_vcpu_tcb_validE)
     apply (rename_tac s r s')
     apply (drule_tac x="(=) (arch_state s)" in meta_spec)
     apply fastforce
    apply (rename_tac s r s')
    apply (drule_tac x="(=) (tcb_vcpu (tcb_arch (the (get_tcb (cur_thread s) s))) )" in meta_spec)
    apply (fastforce simp: cur_thread_tcb_vcpu_def)
   apply fastforce+
  done

lemma set_object_not_cur_thread_arch_vcpu_tcb_valid:
  "\<lbrace>arch_vcpu_tcb_valid and ((\<noteq>) addr) \<circ> cur_thread\<rbrace> set_object addr obj \<lbrace>\<lambda>_. arch_vcpu_tcb_valid\<rbrace>"
   apply (wpsimp simp: set_object_def arch_vcpu_tcb_valid_def wp: hoare_drop_imp)
   apply (clarsimp simp: cur_tcb_def obj_at_def)
  done

lemma set_object_cur_thread_arch_vcpu_tcb_valid:
  "\<lbrace>arch_vcpu_tcb_valid and ((=) addr) \<circ> cur_thread and (\<lambda>_. is_tcb obj)
    and (\<lambda>s. ARM_A.tcb_vcpu (tcb_arch (case obj of TCB tcb \<Rightarrow> tcb))
               = cur_vcpu_to_tcb_vcpu (ARM_A.arm_current_vcpu (arch_state s)))
    \<rbrace> set_object addr obj \<lbrace>\<lambda>_. arch_vcpu_tcb_valid\<rbrace>"
  by (wpsimp simp: set_object_def arch_vcpu_tcb_valid_def wp: hoare_drop_imp)
     (clarsimp simp: cur_tcb_def obj_at_def arch_vcpu_tcb_valid_obj_def)

lemmas set_object_arch_vcpu_tcb_valid_gen =
         hoare_pre_disj[OF set_object_not_cur_thread_arch_vcpu_tcb_valid(1)
                           set_object_cur_thread_arch_vcpu_tcb_valid(1)]

lemma as_user_arch_vcpu_tcb_valid[wp]:
  "\<lbrace>arch_vcpu_tcb_valid \<rbrace> as_user tcb_ptr f \<lbrace>\<lambda>_. arch_vcpu_tcb_valid\<rbrace>"
  unfolding as_user_def
  apply (wpsimp wp: set_object_arch_vcpu_tcb_valid_gen)
  apply (clarsimp simp:  arch_vcpu_tcb_valid_kheap_unfold arch_tcb_context_set_def)
done

lemma set_thread_state_arch_vcpu_tcb_valid[wp]:
 "\<lbrace>arch_vcpu_tcb_valid\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. arch_vcpu_tcb_valid\<rbrace>"
  unfolding set_thread_state_def
  apply (wpsimp wp: set_object_arch_vcpu_tcb_valid_gen dxo_wp_weak)
  apply (clarsimp simp: arch_vcpu_tcb_valid_kheap_unfold)
  done

lemma activate_thread_arch_vcpu_tcb_valid[wp]:
 "\<lbrace>arch_vcpu_tcb_valid\<rbrace> activate_thread \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid \<rbrace>"
  unfolding activate_thread_def
  by (wpsimp wp: gts_wp simp: ARM_A.arch_activate_idle_thread_def)

lemma do_machine_op_lift:
  "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>machine_state := x\<rparr>)) \<Longrightarrow>
    \<lbrace>\<lambda>s. P s \<rbrace> do_machine_op f \<lbrace>\<lambda>r s. P s\<rbrace>"
  unfolding do_machine_op_def
  by (wpsimp simp: arch_vcpu_tcb_valid_kheap_unfold)

lemma dmo_arch_vcpu_tcb_valid[wp]:
  "do_machine_op f \<lbrace>arch_vcpu_tcb_valid\<rbrace>"
  unfolding do_machine_op_def
  by (wpsimp simp: arch_vcpu_tcb_valid_kheap_unfold)

lemma obj_set_prop_not_at:
 "\<lbrace>\<lambda>s. P (obj_at P' p1 s) \<and> p1 \<noteq> p2 \<rbrace> set_object p2 obj \<lbrace>\<lambda>rv s. P (obj_at P' p1 s)\<rbrace>"
 by (wpsimp simp: set_object_def obj_at_def wp: hoare_drop_imp)

lemma vcpu_switch_idle_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. tcb_at thread s \<and> idle_thread s = thread  \<rbrace>
     vcpu_switch None
  \<lbrace>\<lambda>y s. tcb_at thread s \<rbrace>"
 by (wpsimp simp: vcpu_switch_def vcpu_disable_def)

lemma set_vcpu_obj_at_wp:
  "\<lbrace> \<lambda>s. obj_at (\<lambda>obj. \<forall>t. obj = TCB t \<longrightarrow> tcb_vcpu (tcb_arch t) = None) thread s \<rbrace>
     set_vcpu x1 h
  \<lbrace>\<lambda>xc. obj_at (\<lambda>obj. \<forall>t. obj = TCB t \<longrightarrow> tcb_vcpu (tcb_arch t) = None) thread\<rbrace>"
  apply (clarsimp simp add: set_vcpu_def set_object_def)
  apply (wpsimp wp: get_object_wp)
  apply (clarsimp simp add: in_get in_bind in_put obj_at_def)
  done

lemma set_vcpu_obj_at_tcb_arch: (* generalise? this holds except when the ko is a vcpu *)
  "\<lbrace>\<lambda>s. P (obj_at (\<lambda>a. \<forall>tcb. a = TCB tcb \<longrightarrow> P' tcb) t s) \<rbrace>
      set_vcpu p v
   \<lbrace>\<lambda>_ s. P (obj_at (\<lambda>a. \<forall>tcb. a = TCB tcb \<longrightarrow> P' tcb) t s) \<rbrace>"
  apply (clarsimp simp add: set_vcpu_def set_object_def)
  apply (wpsimp wp: get_object_wp)
  apply (clarsimp simp add: in_get in_bind in_put obj_at_def)
  done

crunch obj_at_tcb_arch[wp]:
  vcpu_save, vcpu_restore, vcpu_disable, arm_context_switch
  "\<lambda>s.  P (obj_at (\<lambda>a. \<forall>tcb. a = TCB tcb \<longrightarrow> P' tcb) t s)"
  (simp: crunch_simps wp: crunch_wps set_vcpu_obj_at_tcb_arch)

lemma arch_vcpu_tcb_valid_obj_update_simps:
  "arch_vcpu_tcb_valid_obj (arch_state s \<lparr>arm_current_vcpu := Some (x1, False)\<rparr>)
   = (\<lambda>obj. \<forall>t. obj = TCB t \<longrightarrow> tcb_vcpu (tcb_arch t) = None)"
  "arch_vcpu_tcb_valid_obj (arch_state s \<lparr>arm_current_vcpu := Some (x1, True)\<rparr>)
   = (\<lambda>obj. \<forall>t. obj = TCB t \<longrightarrow> tcb_vcpu (tcb_arch t) = Some x1)"
  apply (rule ext, clarsimp simp: arch_vcpu_tcb_valid_obj_def cur_vcpu_to_tcb_vcpu_def obj_at_def)+
  done

lemma vcpu_switch_obj_at_arch_vcpu_tcb_valid_obj:
 "\<lbrace>\<lambda>s. obj_at (\<lambda>obj. \<forall>t. obj = TCB t \<longrightarrow> ARM_A.tcb_vcpu (tcb_arch t) = vcpu) thread s \<rbrace>
  vcpu_switch vcpu
  \<lbrace>\<lambda>xa s. obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) thread s\<rbrace>"
  supply if_split [split del]
  apply (simp add: vcpu_switch_def)
  apply (wpsimp simp: arch_vcpu_tcb_valid_obj_update_simps)
  apply (case_tac vcpu; clarsimp simp: cur_vcpu_to_tcb_vcpu_def obj_at_def arch_vcpu_tcb_valid_obj_def
                                split: if_splits)
  done

lemma vcpu_switch_None_wp:
 "\<lbrace>\<top>\<rbrace>
  vcpu_switch None
  \<lbrace>\<lambda>r s. cur_vcpu_to_tcb_vcpu (arm_current_vcpu (arch_state s)) = None \<rbrace>"
 by (wpsimp simp: vcpu_switch_def vcpu_disable_def cur_vcpu_to_tcb_vcpu_def )

lemma vcpu_switch_valid_arch_idle_wp:
 "vcpu_switch vcpu \<lbrace>\<lambda>s. valid_arch_idle s\<rbrace>"
  apply (clarsimp simp: valid_arch_idle_def)
  apply (rule hoare_weaken_pre)
   apply wps
   apply (wpsimp simp: vcpu_switch_def vcpu_disable_def save_virt_timer_def cur_vcpu_to_tcb_vcpu_def)
  apply (clarsimp simp: valid_arch_idle_def)
  done

lemma store_hw_asid_lift:
  assumes aam: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_map:= x\<rparr>\<rparr>))"
  and     aht: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_hwasid_table:= x\<rparr>\<rparr>))"
  shows "\<lbrace>\<lambda>s. P s \<rbrace> store_hw_asid a b \<lbrace>\<lambda>_ s. P s\<rbrace>"
  unfolding store_hw_asid_def
  apply (wpsimp simp: find_pd_for_asid_assert_def find_pd_for_asid_assert_def find_pd_for_asid_def)
  apply (drule aam)
  apply (drule aht)
  apply simp
  done

lemma invalidate_asid_lift:
 "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_map:= x\<rparr>\<rparr>)) \<Longrightarrow>
  \<lbrace>\<lambda>s. P s \<rbrace> invalidate_asid asid \<lbrace>\<lambda>r s. P s\<rbrace>"
  by (wpsimp simp: invalidate_asid_def )

lemma find_free_hw_asid_lift:
  assumes ms:"(\<And>s x. P s \<Longrightarrow> P (s\<lparr>machine_state := x\<rparr>))"
  and     aam: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_map:= x\<rparr>\<rparr>))"
  and     aht: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_hwasid_table:= x\<rparr>\<rparr>))"
  and     ana: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_next_asid:= x\<rparr>\<rparr>))"
  shows "\<lbrace>\<lambda>s. P s \<rbrace> find_free_hw_asid \<lbrace>\<lambda>_ s. P s\<rbrace>"
  apply (wpsimp simp: find_free_hw_asid_def invalidate_hw_asid_entry_def )
       apply (rule do_machine_op_lift)
       apply clarsimp
       apply (rename_tac hw_asid_table next_asid s x)
       apply (drule_tac x=x in ms)
       apply (drule_tac x="\<lambda>a. if a = next_asid then None else arm_hwasid_table (arch_state s) a" in aht)
       apply (erule rsubst[where P=P])
       apply clarsimp
      apply (rule invalidate_asid_lift)
      apply (drule_tac x=x in aam)
      apply (erule rsubst[where P=P])
      apply clarsimp
     apply wpsimp
    apply (wpsimp wp: gets_wp)+
  apply (drule_tac x="arm_next_asid (arch_state s) + 1" in ana)
  apply (drule_tac x="\<lambda>a. if a = arm_next_asid (arch_state s) then None else arm_hwasid_table (arch_state s) a" in aht)
  apply (erule rsubst[where P=P])
  apply clarsimp
  done

lemma get_hw_asid_lift:
  assumes ms:"(\<And>s x. P s \<Longrightarrow> P (s\<lparr>machine_state := x\<rparr>))"
  and     aam: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_map:= x\<rparr>\<rparr>))"
  and     aht: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_hwasid_table:= x\<rparr>\<rparr>))"
  and     ana: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_next_asid:= x\<rparr>\<rparr>))"
  shows "\<lbrace>\<lambda>s. P s \<rbrace> get_hw_asid asid \<lbrace>\<lambda>_ s. P s\<rbrace>"
  unfolding get_hw_asid_def
  apply (wpsimp simp: arch_vcpu_tcb_valid_kheap_unfold wp: store_hw_asid_lift)
       apply (simp add: aam )
      apply (simp add: aht)
     apply (rule find_free_hw_asid_lift)
        apply (simp add: assms)+
    apply (wpsimp )
   apply clarsimp
   apply (wpsimp wp: load_hw_asid_wp)
  apply assumption
  done

lemma  arm_context_switch_lift:
  assumes ms:"(\<And>s x. P s \<Longrightarrow> P (s\<lparr>machine_state := x\<rparr>))"
  and     aam: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_map:= x\<rparr>\<rparr>))"
  and     aht: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_hwasid_table:= x\<rparr>\<rparr>))"
  and     ana: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_next_asid:= x\<rparr>\<rparr>))"
  shows "\<lbrace>P\<rbrace> arm_context_switch pd asid \<lbrace>\<lambda>xb s. P s\<rbrace>"
  apply (wpsimp simp: arm_context_switch_def)
    apply (rule do_machine_op_lift)
    apply (erule ms)
   apply (rule get_hw_asid_lift)
      apply (erule ms aam aht ana)+
    apply assumption
  done

lemma find_pd_for_asid_lift:
  assumes E: "\<And>e s e'. E e s \<Longrightarrow> E e' s"
  and     P: "\<And> s r y. P r s \<Longrightarrow> P y s"
  shows "\<And>r e. \<lbrace>\<lambda>s. P r s \<and> E e s \<rbrace> find_pd_for_asid asid \<lbrace>\<lambda>r s. P r s\<rbrace>, \<lbrace>\<lambda>r s. E r s\<rbrace>"
  apply (simp add: find_pd_for_asid_def)
  apply wpsimp
  apply (fastforce elim: E P)
  done

lemma get_tcb_st_eq[simp]:
 "get_tcb x (s\<lparr>machine_state := xa\<rparr>) = get_tcb x s"
 "get_tcb x (s\<lparr>arch_state := as\<rparr>) = get_tcb x s"
 by (simp add: get_tcb_def)+

lemma hoare_whenE_throwError_wp:
"(\<And>s. Q s \<Longrightarrow> P \<Longrightarrow> E e s) \<Longrightarrow> (\<And>s. Q s \<Longrightarrow> R () s)  \<Longrightarrow> \<lbrace>Q\<rbrace> whenE P (throwError e) \<lbrace>R\<rbrace>, \<lbrace>E\<rbrace>"
  unfolding whenE_def
  by wpsimp

lemma arch_vcpu_tcb_valid_machine_state[simp]:
  "arch_vcpu_tcb_valid s \<Longrightarrow> arch_vcpu_tcb_valid (s\<lparr>machine_state := xb\<rparr>)"
 by (clarsimp simp: arch_vcpu_tcb_valid_def)

lemma obj_at_vcpu_tcb_valid_arch_st_upd[simp]:
  "\<And>x. obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) cur s \<Longrightarrow>
     obj_at (arch_vcpu_tcb_valid_obj (arch_state s\<lparr>arm_asid_map := x\<rparr>)) cur s"
  "\<And>x. obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) cur s \<Longrightarrow>
     obj_at (arch_vcpu_tcb_valid_obj (arch_state s\<lparr>arm_hwasid_table := x\<rparr>)) cur s"
  "\<And>x. obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) cur s \<Longrightarrow>
     obj_at (arch_vcpu_tcb_valid_obj (arch_state s\<lparr>arm_next_asid := x\<rparr>)) cur s"
  by (clarsimp simp: obj_at_def arch_vcpu_tcb_valid_obj_def)+

lemma set_vm_root_idle_vcpu_tcb_valid:
 "\<And>v. \<lbrace>\<lambda>s. x = idle_thread s \<and> tcb_at x s \<and> v = (idle_thread s) \<and>
            valid_arch_idle s \<and>
            cur_vcpu_to_tcb_vcpu (arm_current_vcpu (arch_state s)) = None \<rbrace>
    set_vm_root x
  \<lbrace>\<lambda>x s. obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) v s \<rbrace>"
  apply (simp add: set_vm_root_def)
  apply (wpsimp wp: vcpu_switch_obj_at_arch_vcpu_tcb_valid_obj )
         apply (rule arm_context_switch_lift; clarsimp)
        apply wpsimp
       apply (wpsimp simp: if_apply_def2)
      apply (wpsimp wp: hoare_whenE_throwError_wp)
     apply wpsimp
     apply wps
     apply (rule hoare_conjI, rule hoare_drop_imp, wpsimp)+
   apply (wpsimp wp: get_cap_wp)
  apply (clarsimp simp: obj_at_def is_tcb arch_vcpu_tcb_valid_obj_def valid_arch_idle_def)
 done

lemma vcpu_switch_tcb_at:
"\<lbrace>\<lambda>s. (tcb_at t s)\<rbrace> vcpu_switch x \<lbrace>\<lambda>_ s. (tcb_at t s)\<rbrace>"
  apply (clarsimp simp add: tcb_at_def get_tcb_Some_ko_at valid_def)
  apply (rename_tac tcb)
  apply (cut_tac tcb=tcb in vcpu_switch_tcb_at_arch[where P="\<lambda>v .v", where t=t and param_a=x])
  apply (fastforce simp: valid_def)
 done

lemma arch_switch_to_idle_thread_vcpu_tcb_valid:
 "\<And>v. \<lbrace>\<lambda>s. tcb_at (idle_thread s) s \<and> v = idle_thread s
           \<and> arch_vcpu_tcb_valid s \<and> valid_arch_idle s\<rbrace>
    arch_switch_to_idle_thread
  \<lbrace>\<lambda>x s. obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) v s\<rbrace>"
  apply (simp add: arch_switch_to_idle_thread_def)
  apply (wpsimp simp: arch_vcpu_tcb_valid_def arch_switch_to_idle_thread_def )
  apply (wpsimp wp: set_vm_root_idle_vcpu_tcb_valid)
  apply (wpsimp wp: gets_wp)
  apply simp
  apply (wps)
  apply (wpsimp wp: vcpu_switch_tcb_at  vcpu_switch_None_wp)
  apply (wpsimp wp: vcpu_switch_valid_arch_idle_wp vcpu_switch_tcb_at vcpu_switch_None_wp)
  apply simp
  done

lemma switch_to_idle_thread_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> tcb_at (idle_thread s) s \<and> valid_arch_idle s\<rbrace>
     switch_to_idle_thread
  \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid\<rbrace>"
 unfolding switch_to_idle_thread_def
 by (wpsimp wp: arch_switch_to_idle_thread_vcpu_tcb_valid  simp: arch_vcpu_tcb_valid_def)

lemma getActiveTCB_Some_tcb_at[simp]:
 "getActiveTCB r s = Some y \<Longrightarrow> tcb_at r s"
 by (simp add: tcb_at_def getActiveTCB_def split: option.splits )

lemma idle_thread_tcb_at_invs:
  "invs s \<Longrightarrow> tcb_at (idle_thread s) s"
  apply (drule invs_valid_idle)
  apply (clarsimp simp add:  valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma set_vm_root_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) cur s\<rbrace>
    set_vm_root cur
  \<lbrace>\<lambda>x s. obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) cur s\<rbrace>"
 unfolding set_vm_root_def
  apply (wpsimp wp: )
          apply (rule arm_context_switch_lift; clarsimp)
         apply wpsimp
        apply (wpsimp simp: if_apply_def2)
       apply (wpsimp wp: hoare_whenE_throwError_wp)
     apply (wpsimp wp: get_cap_wp)
    apply wpsimp
   apply clarsimp
  done

lemma arch_switch_to_thread_vcpu_tcb_valid[wp]:
 "\<lbrace>\<top>\<rbrace>
    arch_switch_to_thread cur
  \<lbrace>\<lambda>x s. obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) cur s\<rbrace>"
 unfolding arch_switch_to_thread_def
  apply (wpsimp wp: )
    apply (wpsimp wp: set_vm_root_vcpu_tcb_valid)
   apply (wpsimp wp: vcpu_switch_obj_at_arch_vcpu_tcb_valid_obj)
  apply wpsimp
  apply clarsimp
  done

lemma switch_to_thread_arch_vcpu_tcb_valid[wp]:
 "\<lbrace>\<top> \<rbrace> switch_to_thread cur \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid\<rbrace>"
 unfolding switch_to_thread_def
  apply wpsimp
     apply (wpsimp wp: dxo_wp_weak assert_wp get_wp )
    apply (simp add: arch_vcpu_tcb_valid_def)
   apply (wpsimp wp: dxo_wp_weak assert_wp get_wp)+
  done

lemma schedule_arch_vcpu_tcb_valid:
  "\<lbrace>arch_vcpu_tcb_valid and valid_idle and cur_tcb and valid_arch_idle\<rbrace>
    schedule :: (unit, unit) s_monad
  \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid \<rbrace>"
  unfolding schedule_def
  apply (wpsimp wp: alternative_wp dxo_wp_weak assert_wp)
       apply (wpsimp wp: select_wp)+
     apply (wpsimp wp:  simp: allActiveTCBs_gets)
    apply (wpsimp wp: gets_wp)
   apply (wpsimp wp: gets_wp return_wp alternative_wp switch_to_idle_thread_arch_vcpu_tcb_valid)
  apply (clarsimp simp: tcb_at_invs idle_thread_tcb_at_invs)
  apply (clarsimp simp: valid_idle_def cur_tcb_def pred_tcb_at_def obj_at_def)
  done

lemma cur_thread_tcbp_vcpu_trans_state[simp]:
  "cur_thread_tcb_vcpu (trans_state f s) = cur_thread_tcb_vcpu s"
  by (simp add: cur_thread_tcb_vcpu_def trans_state_def get_tcb_def)

lemma set_endpoint_arch_vcpu_tcb_valid[wp]:
  "set_endpoint r x \<lbrace>arch_vcpu_tcb_valid\<rbrace>"
  apply (wpsimp simp: set_simple_ko_def wp: set_object_wp get_object_wp)
  apply (clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def)
  done

lemma set_notification_arch_vcpu_tcb_valid[wp]:
  "set_notification r x \<lbrace>arch_vcpu_tcb_valid\<rbrace>"
  apply (wpsimp simp: set_simple_ko_def wp: set_object_wp get_object_wp)
  apply (clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def)
  done

lemma set_simple_ko_arch_vcpu_tcb_valid_weak:
  "\<lbrace>arch_vcpu_tcb_valid and (\<lambda>s. r \<noteq> cur_thread s)\<rbrace> set_simple_ko t r x \<lbrace>\<lambda>_. arch_vcpu_tcb_valid\<rbrace>"
  apply (wpsimp simp: set_simple_ko_def wp: set_object_wp get_object_wp)
  apply (clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def)
  done

lemma set_thread_state_obj_at_prop_not_at:
" \<lbrace>\<lambda>s. ref \<noteq> ref' \<and> P (obj_at P' ref' s)\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>rv s. P (obj_at P' ref' s)\<rbrace>"
  by (wpsimp simp: set_thread_state_def wp: dxo_wp_weak obj_set_prop_not_at)

lemma set_message_info_arch_vcpu_tcb_valid[wp]:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s\<rbrace> set_message_info receiver x \<lbrace>\<lambda>y. arch_vcpu_tcb_valid\<rbrace>"
  by (wpsimp simp: set_message_info_def)+

lemma set_extra_badge_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<rbrace> set_extra_badge buffer badge n \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid\<rbrace>"
  apply (wpsimp simp: set_extra_badge_def store_word_offs_def)
  done

lemma update_cdt_arch_vcpu_tcb_valid[wp]:
"\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s\<rbrace> update_cdt f \<lbrace>\<lambda>r s. arch_vcpu_tcb_valid s\<rbrace>"
  by (wpsimp wp: gets_wp simp: arch_vcpu_tcb_valid_def update_cdt_def set_cdt_def)+

lemma set_cap_arch_vcpu_tcb_valid[wp]:
"\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s\<rbrace> set_cap cap p \<lbrace>\<lambda>r s. arch_vcpu_tcb_valid s\<rbrace>"
  by (wpsimp wp:set_object_wp get_object_wp simp: set_cap_def,
      rename_tac x y z,
      case_tac "x = cur_thread s"; clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def)+

lemma arch_vcpu_tcb_valid_is_original_cap_update[simp]:
 "arch_vcpu_tcb_valid (s\<lparr>is_original_cap := g\<rparr>) = arch_vcpu_tcb_valid s"
  by (simp add: trans_state_def arch_vcpu_tcb_valid_def obj_at_def cur_tcb_def)

lemma cap_insert_arch_vcpu_tcb_valid[wp]:
  "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s\<rbrace> cap_insert cap src dest \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s\<rbrace>"
  apply (simp add: cap_insert_def)
  apply (wpsimp wp:dxo_wp_weak set_cap_tcb simp:   | rule conjI | wps)+
       apply (rule conjI | wpsimp simp: set_untyped_cap_as_full_def)+
        apply (rule conjI | wpsimp simp: set_cap_tcb | wps)+
    apply (wpsimp wp: hoare_drop_imps get_cap_wp )
   apply (wpsimp wp: hoare_drop_imps get_cap_wp )
  apply (clarsimp simp: arch_vcpu_tcb_valid_def)
  done

lemma setup_caller_cap_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s\<rbrace>
     setup_caller_cap sender receiver grant
   \<lbrace>\<lambda>r. arch_vcpu_tcb_valid\<rbrace>"
  supply if_split [split del]
  apply (wpsimp simp: setup_caller_cap_def wp: cap_insert_arch_vcpu_tcb_valid set_thread_state_arch_vcpu_tcb_valid)
  done

(* FIXME cleanup *)
lemma transfer_caps_loop_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s\<rbrace>
   transfer_caps_loop ep rcv_buffer n caps slots mi
  \<lbrace>\<lambda>r. arch_vcpu_tcb_valid\<rbrace>"
  supply if_split [split del]
  apply (induct caps arbitrary: slots n mi, simp)
   apply wpsimp
  apply (rule hoare_pre)
   apply (wp hoare_vcg_const_imp_lift hoare_vcg_const_Ball_lift
              derive_cap_is_derived_foo
             hoare_drop_imps
        | assumption | simp)+
  apply (wpsimp wp: set_extra_badge_arch_vcpu_tcb_valid set_extra_badge_typ_ats)
   apply (wp hoare_vcg_const_imp_lift hoare_vcg_const_Ball_lift
              derive_cap_is_derived_foo
             hoare_drop_imps
        | assumption | simp)+
done



lemma transfer_cap_arch_vcpu_tcb_valid:
"\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<rbrace>
  transfer_caps mi caps ep receiver recv_buffer
 \<lbrace>\<lambda>r. arch_vcpu_tcb_valid\<rbrace>"
  by (wpsimp simp: transfer_caps_def wp: transfer_caps_loop_arch_vcpu_tcb_valid )

lemma store_word_offs_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s\<rbrace>
   store_word_offs ptr offs v
  \<lbrace>\<lambda>buf_mrs. arch_vcpu_tcb_valid\<rbrace>"
  unfolding arch_vcpu_tcb_valid_def
  by (rule hoare_pre)
     (wps | wpsimp wp: store_word_offs_obj_at_P)+

lemma copy_mrs_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s\<rbrace>
    copy_mrs sender sbuf receiver rbuf n
  \<lbrace>\<lambda>mrs_transferred s. arch_vcpu_tcb_valid s\<rbrace>"
  supply if_split [split del]
  by (wpsimp simp: copy_mrs_def wp: mapM_wp' store_word_offs_arch_vcpu_tcb_valid)

lemma do_normal_transfer_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<rbrace>
   do_normal_transfer sender send_buffer ep badge grant receiver recv_buffer
  \<lbrace>\<lambda>rv s. arch_vcpu_tcb_valid s \<rbrace>"
  apply (wpsimp simp: do_normal_transfer_def wp: set_message_info_arch_vcpu_tcb_valid
            transfer_cap_arch_vcpu_tcb_valid copy_mrs_arch_vcpu_tcb_valid
              )
done

(* FIXME: zipWithM_x_inv' should replace zipWithM_x_inv as it's more general *)
lemma zipWithM_x_inv':
  assumes step: "\<And>x y. \<lbrace>P\<rbrace> m x y \<lbrace>\<lambda>rv. P\<rbrace>"
  shows " \<lbrace>P\<rbrace> zipWithM_x m xs ys \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (induct ys arbitrary:xs)
  apply (simp add: zipWithM_x_def sequence_x_def zipWith_def)
  apply (case_tac xs ;clarsimp)
  apply (wpsimp wp: step simp: zipWithM_x_def zipWith_def sequence_x_def)
  apply (rename_tac y ys x xs)
  apply (drule_tac x=xs in meta_spec)
  apply (wpsimp wp: step simp: zipWithM_x_def zipWith_def sequence_x_def)
  done

lemma set_mrs_arch_vcpu_tcb_valid[wp]:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s\<rbrace>
    set_mrs thread buf msgs
  \<lbrace>\<lambda>sent. arch_vcpu_tcb_valid\<rbrace>"
  supply if_split [split del]
  apply (wpsimp simp: set_mrs_def wp: zipWithM_x_inv' store_word_offs_arch_vcpu_tcb_valid)
    apply (wpsimp wp: set_object_wp)
   apply wpsimp
  apply clarsimp
  apply (clarsimp simp: arch_vcpu_tcb_valid_def arch_vcpu_tcb_valid_obj_def
                        arch_tcb_context_set_def obj_at_def
                        arch_tcb_set_registers_def split: if_split)
  apply (simp add: is_tcb get_tcb_def split: kernel_object.splits)
  done

lemma make_fault_msg_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s\<rbrace>
   make_fault_msg f sender
  \<lbrace>\<lambda>r s. arch_vcpu_tcb_valid s\<rbrace>"
  apply (case_tac f ; wpsimp)
  apply (rule conjI;clarsimp)
  apply wpsimp
  apply (rule hoare_pre)
  apply wpsimp
  apply simp
  apply (rename_tac x, case_tac x; (wpsimp)+)
done


lemma do_fault_transfer_arch_vcpu_tcb_valid:
"\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s\<rbrace>
  do_fault_transfer badge sender receiver buf
  \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid\<rbrace>"
  apply (wpsimp simp: do_fault_transfer_def
           wp:  hoare_drop_imps make_fault_msg_tcb_at
               set_mrs_arch_vcpu_tcb_valid  make_fault_msg_arch_vcpu_tcb_valid)
done

lemma do_ipc_transfer_arch_vcpu_tcb_valid[wp]:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s\<rbrace>
   do_ipc_transfer sender ep badge grant receiver
  \<lbrace>\<lambda>rv s. arch_vcpu_tcb_valid s \<rbrace>"
  by (wpsimp simp: do_ipc_transfer_def wp: do_normal_transfer_arch_vcpu_tcb_valid
        do_fault_transfer_arch_vcpu_tcb_valid)

lemma send_ipc_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s \<and> ep_at epptr s\<rbrace>
   send_ipc block call badge can_grant can_grant_reply thread epptr
  \<lbrace>\<lambda>r. arch_vcpu_tcb_valid\<rbrace>"
  supply if_split [split del]
  apply (wpsimp simp: send_ipc_def wp: )
          apply (wpsimp wp: setup_caller_cap_arch_vcpu_tcb_valid)
  apply (wpsimp wp: )
  apply (simp add: if_apply_def2)
  apply (wpsimp wp: hoare_drop_imps dxo_wp_weak)
  apply wps
  apply (wpsimp wp: set_thread_state_arch_vcpu_tcb_valid)
  apply (wpsimp wp: )
  apply (wpsimp wp: do_ipc_transfer_arch_vcpu_tcb_valid)
  apply (wpsimp wp: hoare_drop_imps)
  apply wpsimp
  apply wps
  apply (wpsimp wp: hoare_drop_imps hoare_vcg_all_lift)
  apply (clarsimp simp: obj_at_def is_ep)
done

lemma thread_set_arch_vcpu_tcb_valid_gen:
 "\<forall>y. tcb_vcpu (tcb_arch (h y)) = tcb_vcpu (tcb_arch y) \<Longrightarrow>
  \<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<rbrace> thread_set h tptr \<lbrace>\<lambda>rv s. arch_vcpu_tcb_valid s \<rbrace>"
  apply (wpsimp simp: thread_set_def)
  apply (wpsimp wp: set_object_wp)
  apply wpsimp
  apply (clarsimp simp: arch_vcpu_tcb_valid_def)
  apply (case_tac "tptr = cur_thread s" )
  apply (clarsimp simp: arch_vcpu_tcb_valid_obj_def obj_at_def get_tcb_def split:kernel_object.splits )+
  done

lemma thread_set_tcb_fault_upd_arch_vcpu_tcb_valid[wp]:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<rbrace> thread_set (tcb_fault_update h) tptr \<lbrace>\<lambda>rv s. arch_vcpu_tcb_valid s \<rbrace>"
  by (rule thread_set_arch_vcpu_tcb_valid_gen, simp)

lemma thread_set_ep_at:
  "\<lbrace>\<lambda>s. tcb_at tptr s \<and> ep_at epptr s\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. ep_at epptr\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wpsimp wp: set_object_wp simp: is_ep is_tcb)
  apply (case_tac "epptr = tptr"; clarsimp simp: obj_at_def is_ep)
done

lemma send_fault_ipc_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s. valid_objs s \<and> arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s \<and> tcb_at tptr s\<rbrace>
     send_fault_ipc tptr fault
   \<lbrace>\<lambda>r. arch_vcpu_tcb_valid\<rbrace>"
  apply (simp add: send_fault_ipc_def)
  apply (wpsimp simp: Let_def)
  apply (wpsimp simp: send_fault_ipc_def Let_def wp: send_ipc_arch_vcpu_tcb_valid
        thread_set_tcb_fault_upd_arch_vcpu_tcb_valid)
  apply wps
  apply (wpsimp wp: thread_set_tcb_fault_upd_arch_vcpu_tcb_valid thread_set_ep_at)
  apply wpsimp+
  apply (rule hoare_post_imp_R[where Q'="\<lambda>r s. arch_vcpu_tcb_valid s \<and> valid_cap r s \<and> tcb_at (cur_thread s) s \<and> tcb_at tptr s"])
  apply wpsimp
  apply (clarsimp simp: valid_cap_def)
  apply wpsimp
  apply clarsimp
done

crunch cur_thread[wp]: send_fault_ipc "\<lambda>s::'a::state_ext state. P (cur_thread s)"
  (simp: Let_def if_apply_def2 wp: crunch_wps dxo_wp_weak  )

lemma send_fault_ipc_arch_vcpu_tcb_valid_cur_thread:
   "\<lbrace>\<lambda>s. valid_objs s \<and> arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s \<and> tcb_at tptr s\<rbrace>
     send_fault_ipc tptr fault
   \<lbrace>\<lambda>r s. arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s\<rbrace>"
 apply (rule hoare_weaken_pre)
 apply wps
 apply (wpsimp wp: send_fault_ipc_arch_vcpu_tcb_valid sfi_tcb_at)+
done

lemma rfk_arch_vcpu_tcb_valid_cur_thread:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s\<rbrace>
   reply_from_kernel t r
  \<lbrace>\<lambda>rv s. arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s\<rbrace>"
 unfolding reply_from_kernel_def
 by (wpsimp | wps)+

lemmas hoare_conjD1' = hoare_conjD1[simplified pred_conj_def]

crunch cur_thread[wp]:
  send_signal,
  restart,
  suspend,
  arch_post_modify_registers
  "\<lambda>s::'a::state_ext state. P (cur_thread s)"
  (simp: Let_def if_apply_def2 wp: crunch_wps dxo_wp_weak select_wp )

lemma validE_valid_conj:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_ s. Q s \<and> E s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>, \<lbrace>\<lambda>_. E\<rbrace>"
  by (fastforce simp add: valid_def validE_def split:sum.splits)

lemma handle_fault_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. valid_objs s \<and> arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s \<rbrace>
    handle_fault thread ft
  \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid\<rbrace>"
  unfolding handle_fault_def
  by (wpsimp simp: handle_double_fault_def
             wp: hoare_conjD1'[OF send_fault_ipc_arch_vcpu_tcb_valid_cur_thread])

lemma set_object_tcb_st_arch_vcpu_tcb_valid:
"\<lbrace>\<lambda>s. ko_at (TCB tcb) thread s \<and> arch_vcpu_tcb_valid s \<rbrace>
   set_object thread (TCB (tcb\<lparr>tcb_state := st\<rparr>))
 \<lbrace>\<lambda>xc. arch_vcpu_tcb_valid\<rbrace>"
  apply (wpsimp wp: set_object_wp)
  apply (simp add: obj_at_def arch_vcpu_tcb_valid_def)
  apply (case_tac "thread = cur_thread s" ; clarsimp simp: arch_vcpu_tcb_valid_obj_def)
 done

lemma perform_invocation_cur_thread[unfolded cur_tcb_def,wp]:
 "\<lbrace> invs and ct_active and valid_invocation invoc \<rbrace> perform_invocation block call invoc \<lbrace>\<lambda>_ s. cur_tcb s \<rbrace>"
  apply (strengthen invs_cur)
  apply (wpsimp wp: pinv_invs)
done

lemma create_cap_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s\<rbrace>
    create_cap  type bits untyped is_device slotnref
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s\<rbrace>"
  unfolding create_cap_def
  apply (wpsimp wp: dxo_wp_weak simp: set_cdt_def)
  apply (clarsimp simp: arch_vcpu_tcb_valid_def)
  done

lemma init_arch_objects_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s\<rbrace>
    init_arch_objects new_type ptr num_objects obj_sz refs
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s\<rbrace>"
  unfolding init_arch_objects_def
  by (wps | wpsimp wp: mapM_x_wp_inv
                   simp: copy_global_mappings_def | assumption)+

lemma obj_at_not_in_foldr:
  "obj_at P p s \<Longrightarrow> p \<notin> set xs \<Longrightarrow> obj_at P p (s \<lparr> kheap := foldr (\<lambda>p ps. ps (p \<mapsto> obj)) xs (kheap s) \<rparr>)"
  by (clarsimp simp: obj_at_def foldr_upd_app_if)

lemma retype_region_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> cur_thread s \<notin> set (retype_addrs ptr type numObjects o_bits)\<rbrace>
    retype_region ptr numObjects o_bits type dev
  \<lbrace>\<lambda>orefs s. arch_vcpu_tcb_valid s\<rbrace>"
  unfolding retype_region_def
  apply (wpsimp wp: dxo_wp_weak  simp: arch_vcpu_tcb_valid_def simp_del: fun_upd_apply)
  apply (auto simp: retype_addrs_def elim: obj_at_not_in_foldr)
  done

(* FIXME: should mapM*_wp' replace mapM*_wp lemmas *)
lemma mapM_wp':
  assumes x: "\<And>x. x \<in> S \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>"
      and y:  "\<And>v. P v \<Longrightarrow> Q v"
  shows      "set xs \<subseteq> S \<Longrightarrow> \<lbrace>P\<rbrace> mapM f xs \<lbrace>\<lambda>rv. Q\<rbrace>"
  apply (induct xs)
   apply (wpsimp simp: mapM_def sequence_def y)
  apply (simp add: mapM_Cons)
  apply wpsimp
  apply (wpsimp wp: x)+
  done

lemma mapM_x_wp':
  assumes x: "\<And>x. x \<in> S \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>"
      and y: "\<And>v. P v \<Longrightarrow> Q v"
  shows "set xs \<subseteq> S \<Longrightarrow> \<lbrace>P\<rbrace> mapM_x f xs \<lbrace>\<lambda>rv. Q\<rbrace>"
  apply (subst mapM_x_mapM)
    apply (wpsimp wp: mapM_wp' x simp: y)+
 done

lemma mapME_x_inv_wp':
  assumes x: "\<And>x. \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>,\<lbrace>E\<rbrace>"
      and y: "\<And>v. P v \<Longrightarrow> Q v"
  shows      "\<lbrace>P\<rbrace> mapME_x f xs \<lbrace>\<lambda>rv. Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (induct xs)
   apply (simp add: mapME_x_def sequenceE_x_def)
   apply (wp)
   apply (erule y)
  apply (simp add: mapME_x_def sequenceE_x_def)
  apply (fold mapME_x_def sequenceE_x_def)
  apply wp
   apply (rule x)
  apply assumption
  done

lemmas mapM_x_wp_inv' = mapM_x_wp'[where S=UNIV, simplified]

lemma irq_state_independent_top[simp]:
  "irq_state_independent (\<lambda>_. True) = True"
  apply (simp add: irq_state_independent_def)
  done

lemma preemption_point_cur_thread[wp]:
 "\<lbrace>\<lambda>s. Q (cur_thread s) \<rbrace> preemption_point \<lbrace>\<lambda>r s.  Q (cur_thread s)\<rbrace>"
 unfolding preemption_point_def
 by (wpsimp wp: OR_choiceE_weak_wp dxo_wp_weak)

lemma preemption_point_arch_state[wp]:
 "\<lbrace>\<lambda>s. Q (arch_state s) \<rbrace> preemption_point \<lbrace>\<lambda>r s.  Q (arch_state s)\<rbrace>"
 unfolding preemption_point_def
 by (wpsimp wp: OR_choiceE_weak_wp dxo_wp_weak)

lemma preemption_point_obj_at:
 "\<lbrace>\<lambda>s. Q (obj_at P ptr s) \<rbrace> preemption_point \<lbrace>\<lambda>r s.  Q (obj_at P ptr s)\<rbrace>"
 unfolding preemption_point_def
 by (wpsimp wp: OR_choiceE_weak_wp dxo_wp_weak)

lemma preemption_point_arch_vcpu_tcb_valid[wp]:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<rbrace> preemption_point \<lbrace>\<lambda>r s.  arch_vcpu_tcb_valid s\<rbrace>"
  apply (unfold arch_vcpu_tcb_valid_def)
  apply (rule hoare_pre)
  apply wps
  apply (wpsimp wp: preemption_point_obj_at)+
  done

lemma preemption_point_cur_tcb:
 "\<lbrace>\<lambda>s. cur_tcb s \<rbrace> preemption_point \<lbrace>\<lambda>r s.  cur_tcb s\<rbrace>"
  apply (unfold cur_tcb_def)
  apply (rule hoare_pre)
   apply wps
  apply (wpsimp wp: preemption_point_obj_at)+
  done

lemma cur_thread_detype[simp]:
 "cur_thread (detype x s) = cur_thread s"
  by (simp add: detype_def)

lemma delete_objects_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s.  arch_vcpu_tcb_valid s \<and> cur_thread s \<notin> {base..base + 2 ^ sz - 1}\<rbrace>
     delete_objects base sz
   \<lbrace>\<lambda>r s. arch_vcpu_tcb_valid s\<rbrace>"
  unfolding delete_objects_def
  apply (wpsimp simp: arch_vcpu_tcb_valid_def )
  apply wps
  apply (wpsimp wp: do_machine_op_obj_at)
  apply (clarsimp simp:arch_vcpu_tcb_valid_def)
  done

lemma reset_untyped_cap_arch_vcpu_tcb_valid:
 "ui = Retype slot True ptr_base ptr' ty us slots dev \<Longrightarrow>
   \<lbrace>invs and valid_untyped_inv ui and ct_active and arch_vcpu_tcb_valid\<rbrace>
     reset_untyped_cap slot
  \<lbrace>\<lambda>y s. arch_vcpu_tcb_valid s\<rbrace>"
 unfolding reset_untyped_cap_def
  apply (wpsimp wp:  mapME_x_inv_wp
                simp:unless_def| wps)+
  apply (wpsimp wp: hoare_drop_imps delete_objects_arch_vcpu_tcb_valid)
  apply wpsimp+
  apply (wpsimp wp: get_cap_wp)
  apply (clarsimp simp: ct_in_state_def)
  apply (frule invs_iflive)
  apply (drule_tac p="cur_thread s" in if_live_then_nonz_capD)
     apply (clarsimp simp: pred_tcb_at_def)
    apply assumption
   apply (auto simp: live_def)[1]
  apply (drule (1) ex_nonz_cap_to_overlap[where p=slot])
     apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps)
    apply assumption
   apply (clarsimp simp: descendants_range_def)
  apply (clarsimp simp: cte_wp_at_caps_of_state bits_of_def)
  done

lemma invoke_untyped_arch_vcpu_tcb_valid:
  "\<lbrace> invs and ct_active and valid_untyped_inv ui and arch_vcpu_tcb_valid\<rbrace>
    invoke_untyped ui
  \<lbrace>\<lambda>y s. arch_vcpu_tcb_valid s\<rbrace>"
  unfolding invoke_untyped_def mapM_x_defsym
  apply (wpsimp wp: mapM_x_wp_inv create_cap_arch_vcpu_tcb_valid
      init_arch_objects_arch_vcpu_tcb_valid
      retype_region_arch_vcpu_tcb_valid
      reset_untyped_cap_arch_vcpu_tcb_valid)
     apply assumption
    apply wpsimp
   apply wpsimp
   apply (wpsimp wp: reset_untyped_cap_arch_vcpu_tcb_valid)
  apply (intro allI impI conjI)
    apply (clarsimp split: if_split)
    apply fastforce
   apply simp
  apply (subgoal_tac "cur_thread s \<notin> set (retype_addrs xc xd (length xf) xe)")
   apply fastforce
  apply (clarsimp simp: retype_addrs_def)
  apply (clarsimp simp: retype_addrs_def obj_bits_api_def default_arch_object_def image_def ptr_add_def)
  subgoal sorry (* annoying, I don't quite understand this *)
  done

lemma cancel_all_ipc_arch_vcpu_tcb_valid[wp]:
 "\<lbrace>arch_vcpu_tcb_valid \<rbrace>
     cancel_all_ipc f
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  unfolding cancel_all_ipc_def
  apply (wpsimp wp: dxo_wp_weak mapM_x_wp_inv hoare_drop_imp)
  done

crunches invoke_domain
  for arch_vcpu_tcb_valid[wp]: arch_vcpu_tcb_valid
  (wp: crunch_wps dxo_wp_weak)

lemma set_irq_state_arch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     set_irq_state param_a param_b
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  unfolding set_irq_state_def
  apply wpsimp
  by (clarsimp simp: arch_vcpu_tcb_valid_def)

crunches set_irq_state
  for tcb_at[wp]: "tcb_at t"

crunches invoke_irq_control
  for arch_vcpu_tcb_valid[wp]: arch_vcpu_tcb_valid
  (wp: crunch_wps dxo_wp_weak)

lemma blocked_cancel_ipc_arch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     blocked_cancel_ipc a t
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  unfolding blocked_cancel_ipc_def
  by wpsimp

lemma set_bound_notification_arch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     set_bound_notification a b
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  unfolding set_bound_notification_def
  apply (wpsimp wp: set_object_wp)
  by (clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def get_tcb_SomeD)

lemma set_bound_nosdftification_arch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     unbind_maybe_notification a
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  unfolding unbind_maybe_notification_def
  by (wpsimp wp: set_object_wp)

lemma cancel_all_signals_arch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     cancel_all_signals n
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  unfolding cancel_all_signals_def
  by (wpsimp wp: dxo_wp_weak mapM_x_wp_inv get_simple_ko_wp)


lemma set_cdt_arch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     set_cdt s
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  unfolding set_cdt_def
  apply (wpsimp)
  by (clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def get_tcb_SomeD)

crunches fast_finalise
  for arch_vcpu_tcb_valid[wp]: arch_vcpu_tcb_valid
  (wp: crunch_wps ignore: set_object)

crunches post_cap_deletion
  for arch_vcpu_tcb_valid[wp]: arch_vcpu_tcb_valid
  (wp: crunch_wps ignore: set_object)

lemma set_cdt_arsdfch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     empty_slot s c
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  unfolding empty_slot_def
  by (wpsimp wp: set_object_wp dxo_wp_weak mapM_x_wp_inv)

lemma cap_delete_one_arch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     cap_delete_one slot
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  unfolding cap_delete_one_def
  by (wpsimp wp: set_object_wp)

lemma blocked_cancel_ipc_ardfgch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     reply_cancel_ipc t
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  unfolding reply_cancel_ipc_def
  by (wpsimp wp: select_inv hoare_drop_imp thread_set_tcb_fault_upd_arch_vcpu_tcb_valid)

lemma blocked_cancel_ipc_arsdfdfgch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     cancel_signal t n
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  unfolding cancel_signal_def
  by (wpsimp wp: select_inv hoare_drop_imp thread_set_tcb_fault_upd_arch_vcpu_tcb_valid)

lemma cancel_ipc_arch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     cancel_ipc a
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  unfolding cancel_ipc_def
  by (wpsimp wp: hoare_drop_imp)

lemma perform_invosdfcation_arch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     update_waiting_ntfn a b c d
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  unfolding update_waiting_ntfn_def
  by (wpsimp wp: dxo_wp_weak)

lemma send_signal_arch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     send_signal a b
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  unfolding send_signal_def
  by (wpsimp wp: dxo_wp_weak get_simple_ko_wp)

lemma reply_from_kernel_arch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     reply_from_kernel sd x
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  unfolding reply_from_kernel_def
  apply (wpsimp wp:  )
  done

crunches handle_fault_reply
  for arch_vcpu_tcb_valid[wp]: arch_vcpu_tcb_valid

lemma reply_frsdfom_kernel_arch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     do_reply_transfer sender receiver slot grant
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  supply if_split [split del]
  unfolding do_reply_transfer_def
  by (wpsimp wp: dxo_wp_weak hoare_drop_imp)

crunches setup_reply_master for arch_vcpu_tcb_valid[wp]: arch_vcpu_tcb_valid

lemma restart_arch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     restart t
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  supply if_split [split del]
  unfolding restart_def
  by (wpsimp wp: dxo_wp_weak hoare_drop_imp)

lemma suspend_arch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     suspend t
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  supply if_split [split del]
  unfolding suspend_def update_restart_pc_def
  by (wpsimp wp: dxo_wp_weak hoare_drop_imp)

crunches arch_post_modify_registers
  for arch_vcpu_tcb_valid[wp]: arch_vcpu_tcb_valid

lemma unbind_notification_arch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     unbind_notification t
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  supply if_split [split del]
  unfolding unbind_notification_def
  by (wpsimp wp: dxo_wp_weak hoare_drop_imp)

lemma bind_notification_arch_vcpu_tcb_valid[wp]:
 "bind_notification t a \<lbrace>arch_vcpu_tcb_valid\<rbrace>"
  supply if_split [split del]
  unfolding bind_notification_def
  by (wpsimp wp: dxo_wp_weak hoare_drop_imp)

lemma cap_swap_arch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     cap_swap t a aa gg
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  supply if_split [split del]
  unfolding cap_swap_def
  by (wpsimp wp: dxo_wp_weak hoare_drop_imp)

lemma cap_swap_for_delete_arch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     cap_swap_for_delete a aa
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  supply if_split [split del]
  unfolding cap_swap_for_delete_def
  by (wpsimp wp: rec_del_preservation)

crunches vcpu_invalidate_active for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"

lemma sdjkfhhasdfkjh[simp]:
  "cur_vcpu_to_tcb_vcpu None = None"
  unfolding cur_vcpu_to_tcb_vcpu_def
  by simp

lemma vcpu_invalidate_active_GG[wp]:
  "\<lbrace>K (P None)\<rbrace>
   vcpu_invalidate_active
   \<lbrace>\<lambda>rv s. P (cur_vcpu_to_tcb_vcpu (arm_current_vcpu (arch_state s)))\<rbrace>"
  supply if_split [split del]
  unfolding vcpu_invalidate_active_def
  by wpsimp


lemma vcpu_invalidate_active_HH[wp]:
  "\<lbrace>\<lambda>s. obj_at (\<lambda>obj. \<forall>t. obj = TCB t \<longrightarrow> ARM_A.tcb_vcpu (tcb_arch t) = None) (cur_thread s) s\<rbrace>
   vcpu_invalidate_active
   \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid\<rbrace>"
  supply if_split [split del]
  unfolding vcpu_invalidate_active_def
  apply wpsimp
       apply (rule_tac Q="\<lambda>_ s. obj_at (\<lambda>obj. \<forall>t. obj = TCB t \<longrightarrow> ARM_A.tcb_vcpu (tcb_arch t) = None) (cur_thread s) s"
  in hoare_strengthen_post[rotated])
        apply (clarsimp simp: dest!: get_tcb_SomeD simp:
 arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def split: if_splits)
     apply (wpsimp simp: vcpu_disable_def)
      apply wps
      apply wpsimp
      apply wps
      apply wpsimp
    apply wpsimp+
        apply (clarsimp simp: dest!: get_tcb_SomeD simp:
 arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def split: if_splits)
  done

lemma dissociate_vcpu_tcb_arch_vcpu_tcb_valid[wp]:
 "\<lbrace>arch_vcpu_tcb_valid and (\<lambda>s. sym_refs (state_hyp_refs_of s))\<rbrace>
  dissociate_vcpu_tcb v t
  \<lbrace>\<lambda>_. arch_vcpu_tcb_valid\<rbrace>"
  supply if_split [split del]
  unfolding dissociate_vcpu_tcb_def
  apply wpsimp
         apply (wpsimp simp: set_vcpu_def wp: set_object_wp)
        apply (wpsimp simp: wp: arch_thread_set_wp)
       apply (rule_tac Q="\<lambda>_ s. if (t = cur_thread s) then (None =
               cur_vcpu_to_tcb_vcpu
                (arm_current_vcpu (arch_state s))) else (arch_vcpu_tcb_valid s)"
      in hoare_strengthen_post[rotated])
        apply (clarsimp simp: dest!: get_tcb_SomeD simp:
      arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def split: if_splits)
       apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift')
      apply (wpsimp wp: get_vcpu_wp arch_thread_get_wp)+
  apply (intro conjI impI)
   apply (clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def cur_vcpu_to_tcb_vcpu_def
      split: option.splits if_splits)
   apply (case_tac ba; fastforce)
  apply (clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def cur_vcpu_to_tcb_vcpu_def
      split: option.splits if_splits)
  apply (case_tac b; clarsimp)
  apply (subgoal_tac "ko_at (TCB ta) (cur_thread s) s")
   apply (drule (1) hyp_sym_refs_ko_atD[rotated])
   apply (clarsimp simp: obj_at_def state_hyp_refs_of_def)
  apply (clarsimp simp: obj_at_def)
  done

lemma prepare_thread_delete_arch_vcpu_tcb_valid[wp]:
 "\<lbrace>arch_vcpu_tcb_valid and (\<lambda>s. sym_refs (state_hyp_refs_of s))\<rbrace>
  prepare_thread_delete t
  \<lbrace>\<lambda>_. arch_vcpu_tcb_valid\<rbrace>"
  supply if_split [split del]
  unfolding prepare_thread_delete_def
  by (wpsimp wp: hoare_drop_imp)

crunches deleting_irq_handler
  for arch_vcpu_tcb_valid[wp]: arch_vcpu_tcb_valid

lemma set_vm_root_arch_vcpu_tcb_valid[wp]:
  "\<lbrace> arch_vcpu_tcb_valid\<rbrace>
    set_vm_root x14
   \<lbrace>\<lambda>y s. arch_vcpu_tcb_valid s\<rbrace>"
  apply (simp add: set_vm_root_def)
  apply (wpsimp wp: set_object_wp)
  apply (rule arm_context_switch_lift)
          apply (clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def)
          apply (clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def)
          apply (clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def)
          apply (clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def)
  apply (wpsimp wp: get_cap_wp simp: find_pd_for_asid_def)+
  done

lemma sdffsfsfs:
  "\<forall>x. arm_current_vcpu (f x) = arm_current_vcpu x \<Longrightarrow>
   arch_vcpu_tcb_valid (s\<lparr>arch_state := f (arch_state s)\<rparr>) = arch_vcpu_tcb_valid s"
  by (clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def)+

lemma sdfhjkh[simp]:
  "arch_vcpu_tcb_valid (a\<lparr>arch_state := arch_state a \<lparr>arm_asid_table := j\<rparr>\<rparr>) = arch_vcpu_tcb_valid a"
  "arch_vcpu_tcb_valid (a\<lparr>arch_state := arch_state a \<lparr>arm_asid_map := k\<rparr>\<rparr>) = arch_vcpu_tcb_valid a"
  "arch_vcpu_tcb_valid (a\<lparr>arch_state := arch_state a \<lparr>arm_hwasid_table := g\<rparr>\<rparr>) = arch_vcpu_tcb_valid a"
  by (rule sdffsfsfs, simp)+

crunches invalidate_asid_entry, flush_space
  for arch_vcpu_tcb_valid[wp]: arch_vcpu_tcb_valid

crunches delete_asid_pool
  for arch_vcpu_tcb_valid[wp]: arch_vcpu_tcb_valid
  (wp: crunch_wps simp: crunch_simps)


lemma set_pd_arch_vcpu_tcb_valid[wp]:
  "\<lbrace> arch_vcpu_tcb_valid\<rbrace>
    set_pd x14 x13
   \<lbrace>\<lambda>y s. arch_vcpu_tcb_valid s\<rbrace>"
  apply (simp add: set_pd_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def)
  done

lemma set_pt_arch_vcpu_tcb_valid[wp]:
  "\<lbrace> arch_vcpu_tcb_valid\<rbrace>
    set_pt x14 x13
   \<lbrace>\<lambda>y s. arch_vcpu_tcb_valid s\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def)
  done

lemma set_asid_pool_arch_vcpu_tcb_valid[wp]:
  "\<lbrace> arch_vcpu_tcb_valid\<rbrace>
    set_asid_pool x14 x13
   \<lbrace>\<lambda>y s. arch_vcpu_tcb_valid s\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def)
  done

lemma set_vcpu_arch_vcpu_tcb_valid[wp]:
  "\<lbrace> arch_vcpu_tcb_valid\<rbrace>
    set_vcpu x14 a
   \<lbrace>\<lambda>y s. arch_vcpu_tcb_valid s\<rbrace>"
  apply (simp add: set_vcpu_def)
  apply (wpsimp wp: set_object_wp)
          apply (clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def)
  done

lemma set_vm_root_for_flush_arch_vcpu_tcb_valid[wp]:
  "\<lbrace> arch_vcpu_tcb_valid\<rbrace>
    set_vm_root_for_flush x14 a
   \<lbrace>\<lambda>y s. arch_vcpu_tcb_valid s\<rbrace>"
  apply (simp add: set_vm_root_for_flush_def)
  apply (wpsimp wp: set_object_wp)
       apply (rule arm_context_switch_lift;
              clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def)
  apply (wpsimp wp: get_cap_wp simp: find_pd_for_asid_def)+
  done

crunches store_pde, store_pte, load_hw_asid, page_table_mapped, invalidate_tlb_by_asid, flush_page, lookup_pt_slot
  for arch_vcpu_tcb_valid[wp]: arch_vcpu_tcb_valid

(* crunches unmap_page
  for arch_vcpu_tcb_valid[wp]: arch_vcpu_tcb_valid *)
(* FIXME: why does this crunches fail? There are many like it. *)

lemma unmap_page_arch_vcpu_tcb_valid[wp]:
  "\<lbrace> arch_vcpu_tcb_valid\<rbrace>
    unmap_page pgsz asid vptr pptr
   \<lbrace>\<lambda>y s. arch_vcpu_tcb_valid s\<rbrace>"
  apply (simp add: unmap_page_def)
  apply (wpsimp wp: hoare_drop_imps mapM_wp_inv)
  done

crunches unmap_page_table, unmap_page, delete_asid
  for arch_vcpu_tcb_valid[wp]: arch_vcpu_tcb_valid

lemma vcpu_finalise_arch_vcpu_tcb_valid[wp]:
  "\<lbrace>arch_vcpu_tcb_valid and (\<lambda>s. sym_refs (state_hyp_refs_of s))\<rbrace>
    vcpu_finalise f
   \<lbrace>\<lambda>y s. arch_vcpu_tcb_valid s\<rbrace>"
  apply (simp add: vcpu_finalise_def)
  apply (wpsimp wp: hoare_drop_imp)
  done

lemma arch_finalise_cap_arch_vcpu_tcb_valid[wp]:
 "\<lbrace>arch_vcpu_tcb_valid and (\<lambda>s. sym_refs (state_hyp_refs_of s))\<rbrace>
     arch_finalise_cap a aa
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  supply if_split [split del]
  unfolding arch_finalise_cap_def
  by wpsimp

lemma finalise_cap_arch_vcpu_tcb_valid[wp]:
 "\<lbrace>arch_vcpu_tcb_valid\<rbrace>
    finalise_cap a aa
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  supply if_split [split del]
  apply (cases a; wpsimp)
  sorry

lemma cap_delete_arch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     cap_delete a
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  supply if_split [split del]
  unfolding cap_delete_def
  by (wpsimp wp: rec_del_preservation)

lemma set_mcpriority_arch_vcpu_tcb_valid[wp]:
 "\<lbrace> arch_vcpu_tcb_valid \<rbrace>
     set_mcpriority as a
  \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s \<rbrace>"
  supply if_split [split del]
  unfolding set_mcpriority_def
  by (wpsimp wp: thread_set_arch_vcpu_tcb_valid_gen)

lemma invoke_tcb_arch_vcpu_tcb_valid:
  "\<lbrace> invs and ct_active and tcb_inv_wf ui and arch_vcpu_tcb_valid\<rbrace>
    invoke_tcb ui
  \<lbrace>\<lambda>y s. arch_vcpu_tcb_valid s\<rbrace>"
  supply thread_set_arch_vcpu_tcb_valid_gen [wp]
  supply dxo_wp_weak [wp]
  apply (cases ui; simp)
         apply (wpsimp wp:  hoare_drop_imp)
        apply (wpsimp wp:  hoare_drop_imp)
       apply (wpsimp wp: mapM_x_wp_inv  hoare_drop_imp)
      apply (wpsimp wp:  check_cap_inv )
             apply (wpsimp wp: mapM_x_wp_inv  hoare_drop_imp)
            apply (wpsimp wp: mapM_x_wp_inv  hoare_drop_imp )
           apply wpsimp
          apply (wpsimp wp:   hoare_drop_imp )
             apply (wpsimp wp:  check_cap_inv )
            apply (wpsimp wp:   hoare_drop_imp )
            apply (wpsimp wp:  check_cap_inv )
           apply (wpsimp wp:  dxo_wp_weak hoare_drop_imp )
           apply (wpsimp wp:  check_cap_inv )
          apply wpsimp
         apply (wpsimp wp:   hoare_drop_imp )
           apply (wpsimp wp:  check_cap_inv )
           apply (wpsimp wp:  hoare_vcg_imp_lift')
          apply (wpsimp wp:   hoare_drop_imp )
          apply (wpsimp wp: dxo_wp_weak check_cap_inv )
         apply (wpsimp wp:   hoare_drop_imp )
        apply (wpsimp wp:   hoare_drop_imp )
       apply (wpsimp wp:   hoare_drop_imp simp: option_update_thread_def)
      apply (wpsimp wp:  hoare_drop_imp)
     apply (wpsimp wp:  hoare_drop_imp)
    apply (wpsimp wp:  hoare_drop_imp)
   apply (case_tac x72; simp)
    apply (wpsimp wp: dxo_wp_weak hoare_drop_imp)
   apply (wpsimp wp: dxo_wp_weak hoare_drop_imp)
  apply (wpsimp wp: dxo_wp_weak hoare_drop_imp)
  done

lemma invoke_irq_handler_arch_vcpu_tcb_valid:
  "\<lbrace>  arch_vcpu_tcb_valid\<rbrace>
    invoke_irq_handler ui
  \<lbrace>\<lambda>y s. arch_vcpu_tcb_valid s\<rbrace>"
  apply (cases ui; wpsimp)
  done

lemma cap_move_arch_vcpu_tcb_valid [wp]:
  "cap_move a s ss \<lbrace>arch_vcpu_tcb_valid\<rbrace>"
  unfolding cap_move_def
  by (wpsimp wp: dxo_wp_weak hoare_drop_imp)

lemma cancel_badged_sends_arch_vcpu_tcb_valid [wp]:
  "cancel_badged_sends a s \<lbrace>arch_vcpu_tcb_valid\<rbrace>"
  unfolding cancel_badged_sends_def
  by (wpsimp wp: dxo_wp_weak hoare_drop_imp filterM_preserved)

lemma invoke_cnode_arch_vcpu_tcb_valid[wp]:
  "\<lbrace> arch_vcpu_tcb_valid\<rbrace>
    invoke_cnode ui
  \<lbrace>\<lambda>y s. arch_vcpu_tcb_valid s\<rbrace>"
  supply if_split [split del]
  unfolding invoke_cnode_def
  apply (cases ui; wpsimp wp: cap_revoke_preservation2 get_cap_wp)
  done

lemma arch_thread_set_tcb_vcpu_update_Some_wp:
  "\<lbrace>\<lambda>s. if (b = cur_thread s) then (cur_vcpu_to_tcb_vcpu (arm_current_vcpu (arch_state s)) = M) else arch_vcpu_tcb_valid s\<rbrace>
   arch_thread_set (tcb_vcpu_update (\<lambda>_. M)) b
   \<lbrace>\<lambda>_. arch_vcpu_tcb_valid\<rbrace>"
  unfolding arch_thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def
                 split: if_splits)
  done

crunches dissociate_vcpu_tcb for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps)

lemma helper:
  "arch_vcpu_tcb_valid
               (s\<lparr>arch_state :=
                    arm_current_vcpu_update Map.empty
                     (arch_state s)\<rparr>) = obj_at (\<lambda>obj. \<forall>t. obj = TCB t \<longrightarrow>
           ARM_A.tcb_vcpu (tcb_arch t) = None) (cur_thread s) s"
  by (clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def
                        )
lemma vcpu_disablesssssss_arch_vcpu_tcb_valid:
  "vcpu_disable None \<lbrace>\<lambda>s. obj_at (\<lambda>obj. \<forall>t. obj = TCB t \<longrightarrow> tcb_vcpu (tcb_arch t) = None) (cur_thread s) s\<rbrace>"
  apply (simp add: vcpu_disable_def)
  apply (wpsimp wp: set_object_wp arch_thread_set_tcb_vcpu_update_Some_wp simp: helper)
  apply (wps)
  apply (wpsimp wp: set_object_wp arch_thread_set_tcb_vcpu_update_Some_wp simp: helper)
  apply (wps)
   apply (wpsimp wp: set_object_wp arch_thread_set_tcb_vcpu_update_Some_wp simp: helper)
  apply simp
  done

lemma vcpu_invalidate_activesdafa_sdf_wp[wp]:
  "\<lbrace>\<lambda>s. P None\<rbrace>
          vcpu_invalidate_active
          \<lbrace>\<lambda>y s. P (cur_vcpu_to_tcb_vcpu
            (arm_current_vcpu (arch_state s)))\<rbrace>"
  apply (simp add: vcpu_invalidate_active_def)
  by (wpsimp wp: set_object_wp arch_thread_set_tcb_vcpu_update_Some_wp simp: helper
                wp: vcpu_disablesssssss_arch_vcpu_tcb_valid)

lemma vcpu_invalidate_actsdfivesdafa_sdf_wp[wp]:
  "\<lbrace>\<lambda>s. obj_at
           (\<lambda>obj. \<forall>t. obj = TCB t \<longrightarrow>
                      tcb_vcpu (tcb_arch t) = None)
           (cur_thread s) s\<rbrace>
          vcpu_invalidate_active
          \<lbrace>\<lambda>y . arch_vcpu_tcb_valid\<rbrace>"
  apply (simp add: vcpu_invalidate_active_def)
  apply (wpsimp wp: set_object_wp arch_thread_set_tcb_vcpu_update_Some_wp simp: helper
                wp: vcpu_disablesssssss_arch_vcpu_tcb_valid)
  done

lemma dissociate_vcpu_tcbFFFFF:
  "\<lbrace>\<lambda>s. if (\<exists>aa. arm_current_vcpu (arch_state s) = Some (a, aa)) then (False) else (cur_vcpu_to_tcb_vcpu
             (arm_current_vcpu (arch_state s)) = Some asd)\<rbrace>
          dissociate_vcpu_tcb a b
          \<lbrace>\<lambda>y s. cur_vcpu_to_tcb_vcpu
             (arm_current_vcpu (arch_state s)) = Some asd\<rbrace>"
  apply (simp add: dissociate_vcpu_tcb_def)
  apply (wpsimp wp: set_object_wp arch_thread_set_tcb_vcpu_update_Some_wp get_vcpu_wp arch_thread_get_wp)
  done

lemma dissociate_vcpu_tcbGGGGG:
  "\<lbrace>\<lambda>s. if (b = cur_thread s) then (cur_vcpu_to_tcb_vcpu
            (arm_current_vcpu (arch_state s)) =
           None) else (if (\<exists>aa. arm_current_vcpu (arch_state s) = Some (a, aa)) then
  (obj_at
            (\<lambda>obj. \<forall>t. obj = TCB t \<longrightarrow>
                       tcb_vcpu (tcb_arch t) = None)
            (cur_thread s) s) else (arch_vcpu_tcb_valid s))\<rbrace>
          dissociate_vcpu_tcb a b
          \<lbrace>\<lambda>y. arch_vcpu_tcb_valid\<rbrace>"
  supply if_split [split del]
  apply (simp add: dissociate_vcpu_tcb_def)
  apply (wpsimp wp: set_object_wp arch_thread_set_tcb_vcpu_update_Some_wp get_vcpu_wp arch_thread_get_wp
                    hoare_vcg_imp_lift' hoare_vcg_if_lift2)
  done

lemma arch_perform_invocation_arch_vcpu_tcb_valid:
  "\<lbrace>invs and ct_active and valid_vcpu_invocation x6 and arch_vcpu_tcb_valid\<rbrace>
     associate_vcpu_tcb a b
   \<lbrace>\<lambda>y. arch_vcpu_tcb_valid\<rbrace>"
  apply (simp add: associate_vcpu_tcb_def)
  apply wpsimp
  apply (wpsimp wp: set_object_wp arch_thread_set_tcb_vcpu_update_Some_wp dissociate_vcpu_tcbFFFFF
                    dissociate_vcpu_tcbGGGGG
                    hoare_vcg_imp_lift')
  apply (wpsimp wp: set_object_wp arch_thread_set_tcb_vcpu_update_Some_wp dissociate_vcpu_tcbFFFFF
                    dissociate_vcpu_tcbGGGGG
                    hoare_vcg_imp_lift')
     apply (wpsimp wp: get_vcpu_wp)
  apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift)
  oops

crunches vgic_update_lr, read_vcpu_register, invoke_vcpu_write_register for arch_vcpu_tcb_valid[wp]: arch_vcpu_tcb_valid
  (wp: crunch_wps)

lemma perform_vcpu_invocation_arch_vcpu_tcb_valid:
  "\<lbrace>arch_vcpu_tcb_valid\<rbrace>
     associate_vcpu_tcb v t
   \<lbrace>\<lambda>y. arch_vcpu_tcb_valid\<rbrace>"
  unfolding associate_vcpu_tcb_def
  apply wpsimp

lemma perform_vcpu_invocation_arch_vcpu_tcb_valid:
  "\<lbrace>arch_vcpu_tcb_valid\<rbrace>
     perform_vcpu_invocation x6
   \<lbrace>\<lambda>y. arch_vcpu_tcb_valid\<rbrace>"
  apply (simp add: perform_vcpu_invocation_def valid_vcpu_invocation_def)
  apply (case_tac x6; simp)
  subgoal sorry (* non-trivial, maybe impossible. See explanation below. *)
     apply (wpsimp simp: invoke_vcpu_inject_irq_def)
     apply (wpsimp wp: get_cap_wp simp: invoke_vcpu_read_register_def)
   apply (wpsimp simp: invoke_vcpu_inject_irq_def)
   apply (wpsimp simp: invoke_vcpu_ack_vppi_def)
  done

(* At first glance, it seems as though the invocation "VCPUSetTCB vcpu tcb" can
   break the invariant. More investigation is required to confirm/deny this.

   It appears that associate_vcpu_tcb will dissociate the indicated vcpu (resp. tcb) from its
   existing bound tcb (resp. vcpu) before binding them together.
   If it detects that the current vcpu exists, it will invalidate it using vcpu_invalidate_active.
   This will set the current vcpu to None, and the remaining code in dissociate_vcpu_tcb
   will set the vcpu of the associated thread to None. But there is no guarantee that the associated
   thread is the current thread!

   So it appears that the code needs more checks, or we need to strengthen the invariant. What we
   have is cur_thread points to cur_vcpu, we might also need cur_vcpu points to cur_thread.
*)

lemma arch_perform_invocation_arch_vcpu_tcb_valid:
  "\<lbrace> invs and ct_active and valid_arch_inv ui and arch_vcpu_tcb_valid\<rbrace>
    arch_perform_invocation ui
  \<lbrace>\<lambda>y s. arch_vcpu_tcb_valid s\<rbrace>"
  apply (cases ui; simp add: arch_perform_invocation_def)
       apply (simp add: perform_page_table_invocation_def)
       apply (wpsimp wp: dxo_wp_weak hoare_drop_imp mapM_x_wp_inv)
      apply (simp add: perform_page_directory_invocation_def)
      apply (wpsimp wp: dxo_wp_weak hoare_drop_imp mapM_x_wp_inv)
     apply (simp add: perform_page_invocation_def)
     apply (wpsimp wp: dxo_wp_weak hoare_drop_imp mapM_wp_inv)
    apply (simp add: perform_asid_control_invocation_def)
  subgoal sorry (* annoying, but easy *)
   apply (simp add: perform_asid_pool_invocation_def)
   apply (wpsimp wp: get_cap_wp)
  apply (wpsimp wp: perform_vcpu_invocation_arch_vcpu_tcb_valid)
  done

lemma perform_invocation_arch_vcpu_tcb_valid:
"\<lbrace>invs and ct_active and arch_vcpu_tcb_valid
  and valid_invocation c\<rbrace>
  perform_invocation a b c
 \<lbrace>\<lambda>rv s. arch_vcpu_tcb_valid s\<rbrace>"
  apply (case_tac c; simp)
           apply (wpsimp wp: invoke_untyped_arch_vcpu_tcb_valid)
          apply (wpsimp wp: send_ipc_arch_vcpu_tcb_valid)
         apply (wpsimp wp:)
        apply (wpsimp wp:)
       apply (wpsimp wp: invoke_tcb_arch_vcpu_tcb_valid)
      apply wpsimp
     apply (wpsimp wp:)
    apply wpsimp
   apply (wpsimp wp: invoke_irq_handler_arch_vcpu_tcb_valid)
  apply (wpsimp wp: arch_perform_invocation_arch_vcpu_tcb_valid)
  done

lemma handle_call_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> valid_objs s \<and> tcb_at (cur_thread s) s \<rbrace>
  handle_call
 \<lbrace>\<lambda>rv s. arch_vcpu_tcb_valid s\<rbrace>"
  unfolding handle_call_def handle_invocation_def
  apply (wpsimp simp: set_thread_state_def
      wp: dxo_wp_weak set_object_tcb_st_arch_vcpu_tcb_valid  syscall_valid
      handle_fault_arch_vcpu_tcb_valid
      hoare_conjD1'[OF rfk_arch_vcpu_tcb_valid_cur_thread])
                apply (wpsimp wp: simp: get_tcb_ko_atI)
                apply (wpsimp wp: hoare_drop_imps)
               apply wpsimp+
          apply (wpsimp wp: hoare_drop_imps)
         apply clarsimp
         apply (wpsimp wp: perform_invocation_arch_vcpu_tcb_valid)
        apply wpsimp
  oops

lemma handle_send_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> valid_objs s \<and> tcb_at (cur_thread s) s \<rbrace>
  handle_send bl
 \<lbrace>\<lambda>rv s. arch_vcpu_tcb_valid s\<rbrace>"
  supply if_split [split del]
unfolding handle_send_def handle_invocation_def
 apply (wpsimp simp: set_thread_state_def
               wp: dxo_wp_weak set_object_tcb_st_arch_vcpu_tcb_valid  syscall_valid
                   handle_fault_arch_vcpu_tcb_valid
                   hoare_conjD1'[OF rfk_arch_vcpu_tcb_valid_cur_thread])
  apply (wpsimp wp: simp: get_tcb_ko_atI)
              apply (wpsimp wp: hoare_drop_imps)

       apply (wpsimp wp: perform_invocation_arch_vcpu_tcb_valid)
      apply wpsimp
  oops

crunches arch_mask_irq_signal
  for arch_vcpu_tcb_valid[wp]: arch_vcpu_tcb_valid
  (simp: crunch_simps wp: crunch_wps)

crunches vgic_update_lr
  for tcb_at[wp]: "tcb_at ptr"

lemma vgic_maintenance_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> valid_objs s \<and> tcb_at (cur_thread s) s \<rbrace>
  vgic_maintenance
 \<lbrace>\<lambda>rv s. arch_vcpu_tcb_valid s\<rbrace>"
  supply if_split [split del]
  unfolding vgic_maintenance_def
  by (wpsimp wp: dxo_wp_weak handle_fault_arch_vcpu_tcb_valid hoare_vcg_if_lift2 hoare_drop_imp
      | wps)+

lemma vppi_event_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> valid_objs s \<and> tcb_at (cur_thread s) s \<rbrace>
  vppi_event irq
 \<lbrace>\<lambda>rv s. arch_vcpu_tcb_valid s\<rbrace>"
  supply if_split [split del]
  unfolding vppi_event_def
  apply (wpsimp wp: handle_fault_arch_vcpu_tcb_valid)
         apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp)
        apply wpsimp
  find_theorems vcpu_update invs
  oops

lemma handle_send_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> valid_objs s \<and> tcb_at (cur_thread s) s \<rbrace>
  handle_reserved_irq irq
 \<lbrace>\<lambda>rv s. arch_vcpu_tcb_valid s\<rbrace>"
 supply if_split [split del]
unfolding handle_reserved_irq_def
  apply (wpsimp wp: dxo_wp_weak vgic_maintenance_arch_vcpu_tcb_valid)
  oops

lemma handle_send_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> valid_objs s \<and> tcb_at (cur_thread s) s \<rbrace>
  handle_interrupt irq
 \<lbrace>\<lambda>rv s. arch_vcpu_tcb_valid s\<rbrace>"
  supply if_split [split del]
unfolding handle_interrupt_def
 apply (wpsimp wp: dxo_wp_weak)
  oops

lemma handle_event_arch_vcpu_tcb_valid:
"\<lbrace>(\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) and arch_vcpu_tcb_valid and valid_arch_idle and invs\<rbrace>
    (handle_event e) :: (unit,'z::state_ext) p_monad
  \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid \<rbrace>"
  apply (case_tac e ; clarsimp)
       apply (rename_tac se)
  subgoal sorry
      apply (wpsimp wp: handle_fault_arch_vcpu_tcb_valid, fastforce)
      apply (wpsimp wp: handle_fault_arch_vcpu_tcb_valid, fastforce)
    apply (wpsimp wp: handle_fault_arch_vcpu_tcb_valid)
  find_theorems handle_reserved_irq arch_vcpu_tcb_valid

  oops

theorem akernel_arch_vcpu_tcb_valid_inv:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) and arch_vcpu_tcb_valid and valid_arch_idle \<rbrace>
    call_kernel e :: (unit,unit) s_monad
  \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid \<rbrace>"
  unfolding call_kernel_def
  apply (wpsimp wp: schedule_arch_vcpu_tcb_valid activate_invs simp: active_from_running )
  oops

end

