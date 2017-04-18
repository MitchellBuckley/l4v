(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
  Lemmas on arch get/set object etc
*)

theory ArchAcc_R
imports SubMonad_R
begin

(*FIXME move*)
lemma hoare_add_post':
  "\<lbrakk>\<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>; \<lbrace>P''\<rbrace> f \<lbrace>\<lambda>rv s. Q' rv s \<longrightarrow> Q rv s\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P' and P''\<rbrace> f \<lbrace>Q\<rbrace>"
  by (fastforce simp add: valid_def)

context begin

lemma fun_all: "f = f' \<Longrightarrow> (\<forall>s. f s \<longrightarrow> f' s)"
 by simp

lemma distrib_imp:
  "P \<longrightarrow> Q \<and> Q' \<Longrightarrow> ((P \<longrightarrow> Q) \<Longrightarrow> (P \<longrightarrow> Q') \<Longrightarrow> R) \<Longrightarrow> R"
 by simp

method def_to_elim = (drule meta_eq_to_obj_eq, drule fun_all, elim allE, elim distrib_imp)
method simp_to_elim = (drule fun_all, elim allE impE)

end

context Arch begin global_naming ARM_A (*FIXME: arch_split*)

lemma asid_pool_at_ko:
  "asid_pool_at p s \<Longrightarrow> \<exists>pool. ko_at (ArchObj (ARM_A.ASIDPool pool)) p s"
  apply (clarsimp simp: obj_at_def a_type_def)
  apply (case_tac ko, simp_all split: if_split_asm)
  apply (rename_tac arch_kernel_obj)
  apply (case_tac arch_kernel_obj, auto split: if_split_asm)
  done

declare valid_arch_state_def[@def_to_elim, conjuncts]

lemmas valid_arch_state_elims[rule_format, elim!] = conjuncts

lemmas valid_vspace_obj_elims [rule_format, elim!] =
  valid_vspace_obj.simps[@simp_to_elim, @ \<open>(drule bspec)?\<close>]

lemmas valid_arch_obj_elims[rule_format, elim!] =
  valid_vspace_obj_elims [unfolded valid_arch_obj_def[symmetric]]

end

context begin interpretation Arch . (*FIXME: arch_split*)

(*FIXME move *)

lemma pspace_relation_None:
  "\<lbrakk>pspace_relation p p'; p' ptr = None \<rbrakk> \<Longrightarrow> p ptr = None"
  apply (rule not_Some_eq[THEN iffD1, OF allI, OF notI])
  apply (drule(1) pspace_relation_absD)
   apply (case_tac y; clarsimp simp: cte_map_def of_bl_def well_formed_cnode_n_def split: if_splits)
   subgoal for n
    apply (drule spec[of _ ptr])
    apply (drule spec)
    apply clarsimp
    apply (drule spec[of _ "replicate n False"])
    apply (drule mp[OF _ refl])
     apply (drule mp)
    subgoal premises by (induct n; simp)
    apply clarsimp
    done
  subgoal for x
     apply (cases x; clarsimp)
   apply ((drule spec[of _ 0], fastforce)+)[2]
   apply (drule spec[of _ ptr])
   apply (drule spec)
   apply clarsimp
   apply (drule mp[OF _ refl])
   apply (drule spec[of _ 0])
   subgoal for _ sz by (cases sz; simp add: pageBits_def)
   done
  done

lemma no_0_obj'_abstract:
  "(s, s') \<in> state_relation \<Longrightarrow> no_0_obj' s' \<Longrightarrow> kheap s 0 = None"
  by (auto intro: pspace_relation_None simp add: no_0_obj'_def)

declare if_cong[cong]

lemma corres_gets_asid [corres]:
  "corres (\<lambda>a c. a = c o ucast) \<top> \<top> (gets (arm_asid_table \<circ> arch_state)) (gets (armKSASIDTable \<circ> ksArchState))"
  by (simp add: state_relation_def arch_state_relation_def)

lemmas arm_asid_table_related = corres_gets_asid[simplified, rule_format]

lemma asid_low_bits [simp]:
  "asidLowBits = asid_low_bits"
  by (simp add: asid_low_bits_def asidLowBits_def)

lemma get_asid_pool_corres [corres]:
  "p = p' \<Longrightarrow> corres (\<lambda>p p'. p = inv ASIDPool p' o ucast)
          (asid_pool_at p) (asid_pool_at' p')
          (get_asid_pool p) (getObject p')"
  apply (simp add: getObject_def get_asid_pool_def get_object_def split_def)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
   apply (clarsimp simp: typ_at'_def ko_wp_at'_def)
   apply (case_tac ko; simp)
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object, simp_all)[1]
   apply (clarsimp simp: lookupAround2_known1
                         projectKOs)
   apply (clarsimp simp: obj_at'_def projectKOs objBits_simps
                         archObjSize_def)
   apply (erule (1) ps_clear_lookupAround2)
     apply simp
    apply (erule is_aligned_no_overflow)
   apply simp
   apply (clarsimp simp add: objBits_simps archObjSize_def
                      split: option.split)
  apply (clarsimp simp: in_monad loadObject_default_def projectKOs)
  apply (simp add: bind_assoc exec_gets)
  apply (drule asid_pool_at_ko)
  apply (clarsimp simp: obj_at_def)
  apply (simp add: return_def)
  apply (simp add: in_magnitude_check objBits_simps
                   archObjSize_def pageBits_def)
  apply clarsimp
  apply (clarsimp simp: state_relation_def pspace_relation_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: other_obj_relation_def asid_pool_relation_def)
  done

lemma aligned_distinct_obj_atI':
  "\<lbrakk> ksPSpace s x = Some ko; pspace_aligned' s;
      pspace_distinct' s; ko = injectKO v \<rbrakk>
      \<Longrightarrow> ko_at' v x s"
  apply (simp add: obj_at'_def projectKOs project_inject
                   pspace_distinct'_def pspace_aligned'_def)
  apply (drule bspec, erule domI)+
  apply simp
  done

lemmas aligned_distinct_asid_pool_atI'
    = aligned_distinct_obj_atI'[where 'a=asidpool,
                                simplified, OF _ _ _ refl]

lemma aligned_distinct_relation_asid_pool_atI'[elim]:
  "\<lbrakk> asid_pool_at p s; pspace_relation (kheap s) (ksPSpace s');
     pspace_aligned' s'; pspace_distinct' s' \<rbrakk>
        \<Longrightarrow> asid_pool_at' p s'"
  apply (drule asid_pool_at_ko)
  apply (clarsimp simp add: obj_at_def)
  apply (drule(1) pspace_relation_absD)
  apply (clarsimp simp: other_obj_relation_def)
  apply (simp split: Structures_H.kernel_object.split_asm
                     arch_kernel_object.split_asm)
  apply (drule(2) aligned_distinct_asid_pool_atI')
  apply (clarsimp simp: obj_at'_def typ_at'_def ko_wp_at'_def
                        projectKOs)
  done

lemma get_asid_pool_corres':
  "corres (\<lambda>p p'. p = inv ASIDPool p' o ucast)
          (asid_pool_at p) (pspace_aligned' and pspace_distinct')
          (get_asid_pool p) (getObject p)"
  apply (rule stronger_corres_guard_imp,
         rule get_asid_pool_corres)
   apply auto
  done

lemma storePDE_cte_wp_at'[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at' P' p s)\<rbrace>
     storePDE ptr val
   \<lbrace>\<lambda>rv s. P (cte_wp_at' P' p s)\<rbrace>"
  apply (simp add: storePDE_def)
  apply (wp setObject_cte_wp_at2'[where Q="\<top>"])
    apply (clarsimp simp: updateObject_default_def in_monad
                          projectKO_opts_defs projectKOs)
   apply (rule equals0I)
   apply (clarsimp simp: updateObject_default_def in_monad
                         projectKOs projectKO_opts_defs)
  apply simp
  done

lemma storePDE_state_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
     storePDE ptr val
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  unfolding storePDE_def
  by (wp setObject_state_refs_of_eq; clarsimp simp: updateObject_default_def in_monad projectKOs)

lemma storePTE_cte_wp_at'[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at' P' p s)\<rbrace>
     storePTE ptr val
   \<lbrace>\<lambda>rv s. P (cte_wp_at' P' p s)\<rbrace>"
  apply (simp add: storePTE_def)
  apply (wp setObject_cte_wp_at2'[where Q="\<top>"])
    apply (clarsimp simp: updateObject_default_def in_monad
                          projectKO_opts_defs projectKOs)
   apply (rule equals0I)
   apply (clarsimp simp: updateObject_default_def in_monad
                         projectKOs projectKO_opts_defs)
  apply simp
  done

lemma storePTE_state_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
     storePTE ptr val
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  unfolding storePTE_def
  apply (wp setObject_state_refs_of_eq;
         clarsimp simp: updateObject_default_def in_monad
                        projectKOs)
  done

crunch cte_wp_at'[wp]: setIRQState "\<lambda>s. P (cte_wp_at' P' p s)"
crunch inv[wp]: getIRQSlot "P"

lemma set_asid_pool_corres [corres]:
  "p = p' \<Longrightarrow> a = inv ASIDPool a' o ucast \<Longrightarrow>
  corres dc (asid_pool_at p and valid_etcbs) (asid_pool_at' p')
            (set_asid_pool p a) (setObject p' a')"
  apply (simp add: set_asid_pool_def)
  apply (corressimp search: set_other_obj_corres[where P="\<lambda>_. True"]
                        wp: get_object_ret get_object_wp)
  apply (simp add: other_obj_relation_def asid_pool_relation_def)
  apply (clarsimp simp: obj_at_simps )
  by (auto simp: obj_at_simps typ_at_to_obj_at_arches
          split: Structures_A.kernel_object.splits if_splits arch_kernel_obj.splits)

lemma set_asid_pool_corres':
  "a = inv ASIDPool a' o ucast \<Longrightarrow>
  corres dc (asid_pool_at p and valid_etcbs) (pspace_aligned' and pspace_distinct')
            (set_asid_pool p a) (setObject p a')"
  apply (rule stronger_corres_guard_imp[OF set_asid_pool_corres])
   apply auto
  done


lemma pde_relation_aligned_simp:
  "pde_relation_aligned (ucast (p && mask pd_bits >> 2)::12 word) pde pde'
       = pde_relation_aligned ((p::word32) >> 2) pde pde'"
  by (clarsimp simp: pde_relation_aligned_def
              split: ARM_H.pde.splits if_splits)

lemma get_pde_corres [corres]:
  "p = p' \<Longrightarrow> corres (pde_relation_aligned (p >> 2)) (pde_at p) (pde_at' p')
     (get_pde p) (getObject p')"
  apply (simp add: getObject_def get_pde_def get_pd_def get_object_def split_def bind_assoc)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
   apply (clarsimp simp: ko_wp_at'_def typ_at'_def lookupAround2_known1)
   apply (case_tac ko; simp)
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object; simp add: projectKOs)
   apply (clarsimp simp: objBits_def cong: option.case_cong)
   apply (erule (1) ps_clear_lookupAround2)
     apply simp
    apply (erule is_aligned_no_overflow)
    apply (simp add: objBits_simps archObjSize_def word_bits_def)
   apply simp
  apply (clarsimp simp: in_monad loadObject_default_def projectKOs)
  apply (simp add: bind_assoc exec_gets)
  apply (clarsimp simp: pde_at_def obj_at_def)
  apply (clarsimp simp add: a_type_def return_def
                  split: if_split_asm Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: typ_at'_def ko_wp_at'_def)
  apply (simp add: in_magnitude_check objBits_simps archObjSize_def pageBits_def pdeBits_def)
  apply (clarsimp simp: bind_def)
  apply (clarsimp simp: state_relation_def pspace_relation_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: other_obj_relation_def pde_relation_def)
  apply (erule_tac x="(ucast (p && mask pd_bits >> 2))" in allE)
  apply (clarsimp simp: mask_pd_bits_inner_beauty)
  apply (clarsimp simp: obj_at_def pde_relation_aligned_simp)
  done

lemmas aligned_distinct_pde_atI'
    = aligned_distinct_obj_atI'[where 'a=pde,
                                simplified, OF _ _ _ refl]

lemma aligned_distinct_relation_pde_atI'[elim]:
  "\<lbrakk> pde_at p s; pspace_relation (kheap s) (ksPSpace s');
     pspace_aligned' s'; pspace_distinct' s' \<rbrakk>
        \<Longrightarrow> pde_at' p s'"
  apply (clarsimp simp add: pde_at_def obj_at_def a_type_def)
  apply (simp split: Structures_A.kernel_object.split_asm
                     if_split_asm arch_kernel_obj.split_asm)
  apply (drule(1) pspace_relation_absD)
  apply (clarsimp simp: other_obj_relation_def)
  apply (drule_tac x="ucast ((p && mask pd_bits) >> 2)"
                in spec)
  apply (subst(asm) ucast_ucast_len)
   apply (rule shiftr_less_t2n)
   apply (rule less_le_trans, rule and_mask_less_size)
    apply (simp add: word_size pd_bits_def pageBits_def)
   apply (simp add: pd_bits_def pageBits_def)
  apply (simp add: shiftr_shiftl1)
  apply (subst(asm) is_aligned_neg_mask_eq[where n=2])
   apply (erule is_aligned_andI1)
  apply (subst(asm) add.commute,
         subst(asm) word_plus_and_or_coroll2)
  apply (clarsimp simp: pde_relation_def)
  apply (drule(2) aligned_distinct_pde_atI')
  apply (clarsimp simp: obj_at'_def typ_at'_def ko_wp_at'_def
                        projectKOs)
  done

lemma pde_relation_alignedD:
  "\<lbrakk> kheap s (p && ~~ mask pd_bits) = Some (ArchObj (PageDirectory pd));
     pspace_relation (kheap s) (ksPSpace s');
     ksPSpace s' ((p && ~~ mask pd_bits) + (ucast x << 2)) = Some (KOArch (KOPDE pde))\<rbrakk>
     \<Longrightarrow> pde_relation_aligned x (pd x) pde"
  apply (clarsimp simp:pspace_relation_def)
  apply (drule bspec,blast)
  apply (clarsimp simp:pde_relation_def)
  apply (drule_tac x = x in spec)
  apply (clarsimp simp:pde_relation_aligned_def
     split:ARM_H.pde.splits)
  done

lemma pde_at_ksPSpace_not_None:
  "\<lbrakk>kheap (a::('a ::state_ext) state) (p && ~~ mask pd_bits) = Some (ArchObj (PageDirectory pd));
  pd (ucast ((p && ~~ mask 6) && mask pd_bits >> 2)) = pde;
  pspace_relation (kheap a) (ksPSpace (b::kernel_state));
  pspace_aligned' b;pspace_distinct' b\<rbrakk>
  \<Longrightarrow> ksPSpace b ((p && ~~ mask 6)::word32) \<noteq> None"
  apply (drule aligned_distinct_relation_pde_atI'[rotated,where p = "p && ~~ mask 6"])
     apply simp+
   apply (simp add:pde_at_def obj_at_def)
     apply (intro conjI exI)
     apply (simp add:pd_bits_def pageBits_def
       and_not_mask_twice)
    apply (simp add:a_type_simps)
   apply (rule is_aligned_weaken)
    apply (rule is_aligned_neg_mask[OF le_refl])
   apply (simp add:is_aligned_andI1)
  apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
  done

lemma get_master_pde_corres [@lift_corres_args, corres]:
  "corres pde_relation' (pde_at p)
     (pde_at' p and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
      pspace_aligned' and pspace_distinct')
     (get_master_pde p) (getObject p)"
  proof -
    have [simp]: "max pd_bits 6 = pd_bits"
      by (simp add:pd_bits_def pageBits_def)
    have expand: "p && ~~ mask pd_bits = (p && ~~ mask 6) && ~~ mask pd_bits"
      by (simp add: and_not_mask_twice)
    have [simp]: "is_aligned (p && ~~ mask 6 >> 2) 4"
      apply (rule is_aligned_shiftr)
      apply (simp add:is_aligned_neg_mask)
      done
  show ?thesis
    apply (simp add: getObject_def get_pde_def get_pd_def  get_object_def
      split_def bind_assoc pde_relation_aligned_def get_master_pde_def)
    apply (rule corres_no_failI)
     apply (rule no_fail_pre, wp)
     apply (clarsimp simp: ko_wp_at'_def typ_at'_def lookupAround2_known1)
     apply (case_tac ko, simp_all)[1]
     apply (rename_tac arch_kernel_object)
     apply (case_tac arch_kernel_object, simp_all add: projectKOs)[1]
     apply (clarsimp simp: objBits_def cong: option.case_cong)
     apply (erule (1) ps_clear_lookupAround2)
       apply simp
      apply (erule is_aligned_no_overflow)
     apply (simp add: objBits_simps archObjSize_def word_bits_def)
    apply simp
    apply (clarsimp simp: in_monad loadObject_default_def
      projectKOs and_not_mask_twice)
    apply (simp add: bind_assoc exec_gets)
    apply (clarsimp simp: pde_at_def obj_at_def)
    apply (clarsimp split:ARM_A.pde.splits)
    apply (intro conjI impI)
  -- "master_pde = InvaliatePTE"
       apply (clarsimp simp add: a_type_def return_def get_pd_def
                  bind_def get_pde_def get_object_def gets_def get_def
                  split: if_split_asm Structures_A.kernel_object.splits arch_kernel_obj.splits)
       apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
       apply (clarsimp simp: in_magnitude_check objBits_simps archObjSize_def pageBits_def pdeBits_def)
       apply (clarsimp simp:state_relation_def)
       apply (frule_tac x = "(ucast (p && mask pd_bits >> 2))"
                     in pde_relation_alignedD)
         apply assumption
        apply (simp add:mask_pd_bits_inner_beauty)
       apply (clarsimp simp: pde_relation_aligned_def
                      split: if_splits ARM_H.pde.splits)
       apply (drule_tac p' = "p && ~~ mask 6" in valid_duplicates'_D[rotated])
          apply (simp add:is_aligned_neg_mask is_aligned_weaken[where y = 2])
         apply (clarsimp simp: vs_ptr_align_def and_not_mask_twice)
        apply simp
       apply (frule_tac x = "(ucast ((p && ~~ mask 6) && mask pd_bits >> 2))"
                     in pde_relation_alignedD)
         apply assumption
        apply (simp add:expand)
        apply (subst mask_pd_bits_inner_beauty)
         apply (simp add:is_aligned_neg_mask)
        apply assumption
       apply (clarsimp simp: pde_relation_aligned_def
                  is_aligned_mask[where 'a=32, symmetric])

  -- "master_pde = PageTablePDE"
      apply (clarsimp simp add: a_type_def return_def get_pd_def
        bind_def get_pde_def get_object_def gets_def get_def
        split: if_split_asm Structures_A.kernel_object.splits arch_kernel_obj.splits)
      apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
      apply (clarsimp simp: in_magnitude_check objBits_simps archObjSize_def pageBits_def pdeBits_def)
      apply (clarsimp simp:state_relation_def)
      apply (frule_tac x = "(ucast (p && mask pd_bits >> 2))" in pde_relation_alignedD)
        apply assumption
       apply (simp add:mask_pd_bits_inner_beauty)
      apply (clarsimp simp:pde_relation_aligned_def
        split:if_splits ARM_H.pde.splits)
      apply (drule_tac p' = "p && ~~ mask 6" in valid_duplicates'_D[rotated])
         apply (simp add:is_aligned_neg_mask is_aligned_weaken[where y = 2])
        apply (clarsimp simp: vs_ptr_align_def)
       apply (simp add:and_not_mask_twice)
      apply (drule_tac x = "(ucast ((p && ~~ mask 6) && mask pd_bits >> 2))" in pde_relation_alignedD)
        apply assumption
       apply (simp add:expand)
       apply (subst mask_pd_bits_inner_beauty)
        apply (simp add:is_aligned_neg_mask)
       apply assumption
      apply (clarsimp simp:pde_relation_aligned_def
         is_aligned_mask[symmetric])
  -- "master_pde = SectionPDE"
     apply (clarsimp simp add: a_type_def return_def get_pd_def
       bind_def get_pde_def get_object_def gets_def get_def
       split: if_split_asm Structures_A.kernel_object.splits arch_kernel_obj.splits)
     apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
     apply (clarsimp simp: in_magnitude_check objBits_simps archObjSize_def pageBits_def pdeBits_def)
     apply (clarsimp simp:state_relation_def)
     apply (frule_tac x = "(ucast (p && mask pd_bits >> 2))" in pde_relation_alignedD)
       apply assumption
      apply (simp add:mask_pd_bits_inner_beauty)
     apply (clarsimp simp:pde_relation_aligned_def
       split:if_splits ARM_H.pde.splits)
     apply (drule_tac p' = "p && ~~ mask 6" in valid_duplicates'_D[rotated])
        apply (simp add:is_aligned_neg_mask is_aligned_weaken[where y = 2])
       apply (clarsimp simp: vs_ptr_align_def)
      apply (simp add:and_not_mask_twice)
     apply (drule_tac x = "(ucast ((p && ~~ mask 6) && mask pd_bits >> 2))" in pde_relation_alignedD)
       apply assumption
      apply (simp add: expand)
      apply (subst mask_pd_bits_inner_beauty)
       apply (simp add:is_aligned_neg_mask)
      apply assumption
     apply (clarsimp simp:pde_relation_aligned_def
         is_aligned_mask[symmetric])
  -- "master_pde = SuperSectionPDE"
    apply (clarsimp simp add: a_type_def return_def get_pd_def
      bind_def get_pde_def get_object_def gets_def get_def
      split: if_split_asm Structures_A.kernel_object.splits arch_kernel_obj.splits)
    apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
    apply (clarsimp simp: in_magnitude_check objBits_simps archObjSize_def pageBits_def pdeBits_def)
    apply (clarsimp simp:state_relation_def)
    apply (drule_tac s = a and s' = b and p = "p && ~~ mask 6"
      in aligned_distinct_relation_pde_atI'[rotated -1])
       apply (clarsimp simp:pde_at_def obj_at_def
         and_not_mask_twice a_type_simps is_aligned_neg_mask)
      apply simp
     apply simp
    apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
    apply (case_tac ko; simp)
    apply (rename_tac arch_kernel_object)
    apply (case_tac arch_kernel_object; simp add: projectKOs)
    apply clarsimp
    apply (frule_tac x = "(ucast ((p && ~~ mask 6 )&& mask pd_bits >> 2))" in pde_relation_alignedD)
      apply assumption
     apply (simp add: expand)
     apply (subst mask_pd_bits_inner_beauty)
      apply (simp add:is_aligned_neg_mask)
     apply assumption
    apply (rename_tac pde)
    apply (case_tac pde)
     apply (simp add: pde_relation_aligned_def
                      is_aligned_mask[where 'a=32, symmetric])+
     apply clarsimp
    apply (drule_tac p = "p && ~~ mask 6" and p' = p  in valid_duplicates'_D)
       apply assumption
      apply simp
     apply (clarsimp simp: vs_ptr_align_def and_not_mask_twice)
    apply simp
    done
  qed

lemma get_pde_corres' :
  "corres (pde_relation_aligned (p >> 2)) (pde_at p)
     (pspace_aligned' and pspace_distinct')
     (get_pde p) (getObject p)"
  apply (rule stronger_corres_guard_imp,
         rule get_pde_corres)
   apply auto[1]
  apply clarsimp
  apply (rule aligned_distinct_relation_pde_atI')
   apply (simp add:state_relation_def)+
  done

lemma get_master_pde_corres':
  "corres pde_relation' (pde_at p)
     ((\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
      pspace_aligned' and pspace_distinct')
     (get_master_pde p) (getObject p)"
  apply (rule stronger_corres_guard_imp,
         rule get_master_pde_corres)
   apply auto
  done


lemma pte_relation_aligned_simp:
  "pte_relation_aligned (ucast (p && mask pt_bits >> 2)::word8) pde pde' =
   pte_relation_aligned ((p::word32) >> 2) pde pde'"
  by (clarsimp simp: pte_relation_aligned_def
              split: ARM_H.pte.splits if_splits)

lemma get_pte_corres [corres]:
  "p = p' \<Longrightarrow> corres (pte_relation_aligned (p >> 2)) (pte_at p) (pte_at' p')
     (get_pte p) (getObject p')"
  apply (simp add: getObject_def get_pte_def get_pt_def get_object_def split_def bind_assoc)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
   apply (clarsimp simp: ko_wp_at'_def typ_at'_def lookupAround2_known1)
   apply (case_tac ko, simp_all)[1]
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object, simp_all add: projectKOs)[1]
   apply (clarsimp simp: objBits_def cong: option.case_cong)
   apply (erule (1) ps_clear_lookupAround2)
     apply simp
    apply (erule is_aligned_no_overflow)
    apply (simp add: objBits_simps archObjSize_def word_bits_def)
   apply simp
  apply (clarsimp simp: in_monad loadObject_default_def projectKOs)
  apply (simp add: bind_assoc exec_gets)
  apply (clarsimp simp: obj_at_def pte_at_def)
  apply (clarsimp simp add: a_type_def return_def
                  split: if_split_asm Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: typ_at'_def ko_wp_at'_def)
  apply (simp add: in_magnitude_check objBits_simps archObjSize_def pageBits_def pteBits_def)
  apply (clarsimp simp: bind_def)
  apply (clarsimp simp: state_relation_def pspace_relation_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: other_obj_relation_def pte_relation_def)
  apply (erule_tac x="(ucast (p && mask pt_bits >> 2))" in allE)
  apply (clarsimp simp: mask_pt_bits_inner_beauty
                        pte_relation_aligned_simp obj_at_def)
  done

lemma pte_relation_alignedD:
  "\<lbrakk> kheap s (p && ~~ mask pt_bits) = Some (ArchObj (PageTable pt));
     pspace_relation (kheap s) (ksPSpace s');
     ksPSpace s' ((p && ~~ mask pt_bits) + (ucast x << 2)) = Some (KOArch (KOPTE pte))\<rbrakk>
     \<Longrightarrow> pte_relation_aligned x (pt x) pte"
  apply (clarsimp simp:pspace_relation_def)
  apply (drule bspec,blast)
  apply (clarsimp simp:pte_relation_def)
  apply (drule_tac x = x in spec)
  apply clarsimp
  done

lemmas aligned_distinct_pte_atI'
    = aligned_distinct_obj_atI'[where 'a=pte,
                                simplified, OF _ _ _ refl]

lemma aligned_distinct_relation_pte_atI'[elim]:
  "\<lbrakk> pte_at p s; pspace_relation (kheap s) (ksPSpace s');
     pspace_aligned' s'; pspace_distinct' s' \<rbrakk>
        \<Longrightarrow> pte_at' p s'"
  apply (clarsimp simp add: pte_at_def obj_at_def a_type_def)
  apply (simp split: Structures_A.kernel_object.split_asm
                     if_split_asm arch_kernel_obj.split_asm)
  apply (drule(1) pspace_relation_absD)
  apply (clarsimp simp: other_obj_relation_def)
  apply (drule_tac x="ucast ((p && mask pt_bits) >> 2)"
                in spec)
  apply (subst(asm) ucast_ucast_len)
   apply (rule shiftr_less_t2n)
   apply (rule less_le_trans, rule and_mask_less_size)
    apply (simp add: word_size pt_bits_def pageBits_def)
   apply (simp add: pt_bits_def pageBits_def)
  apply (simp add: shiftr_shiftl1)
  apply (subst(asm) is_aligned_neg_mask_eq[where n=2])
   apply (erule is_aligned_andI1)
  apply (subst(asm) add.commute,
         subst(asm) word_plus_and_or_coroll2)
  apply (clarsimp simp: pte_relation_def)
  apply (drule(2) aligned_distinct_pte_atI')
  apply (clarsimp simp: obj_at'_def typ_at'_def ko_wp_at'_def
                        projectKOs)
  done

lemma pte_at_ksPSpace_not_None:
  "\<lbrakk>kheap (a :: ('a ::state_ext) state) (p && ~~ mask pt_bits) = Some (ArchObj (PageTable pt));
  pt (ucast ((p && ~~ mask 6) && mask pt_bits >> 2)) = pte;
  pspace_relation (kheap a) (ksPSpace (b::kernel_state));
  pspace_aligned' b;pspace_distinct' b\<rbrakk>
  \<Longrightarrow> ksPSpace b ((p && ~~ mask 6)::word32) \<noteq> None"
  apply (drule aligned_distinct_relation_pte_atI'[rotated,where p = "p && ~~ mask 6"])
     apply simp+
   apply (simp add:pte_at_def obj_at_def)
     apply (intro conjI exI)
     apply (simp add:pt_bits_def pageBits_def
       and_not_mask_twice)
    apply (simp add:a_type_simps)
   apply (rule is_aligned_weaken)
    apply (rule is_aligned_neg_mask[OF le_refl])
   apply (simp add:is_aligned_andI1)
  apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
  done

lemma get_master_pte_corres [@lift_corres_args, corres]:
  "corres pte_relation' (pte_at p)
     (pte_at' p and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
      pspace_aligned' and pspace_distinct')
     (get_master_pte p) (getObject p)"
  proof -
    have [simp]: "max pt_bits 6 = pt_bits"
      by (simp add:pd_bits_def pageBits_def pt_bits_def)
    have expand: "p && ~~ mask pt_bits = (p && ~~ mask 6) && ~~ mask pt_bits"
      by (simp add: and_not_mask_twice)
    have [simp]: "is_aligned (p && ~~ mask 6 >> 2) 4"
      apply (rule is_aligned_shiftr)
      apply (simp add:is_aligned_neg_mask)
      done
  show ?thesis
    apply (simp add: getObject_def get_pte_def get_pt_def  get_object_def
      split_def bind_assoc pte_relation_aligned_def get_master_pte_def)
    apply (rule corres_no_failI)
     apply (rule no_fail_pre, wp)
     apply (clarsimp simp: ko_wp_at'_def typ_at'_def lookupAround2_known1)
     apply (case_tac ko, simp_all)[1]
     apply (rename_tac arch_kernel_object)
     apply (case_tac arch_kernel_object, simp_all add: projectKOs)[1]
     apply (clarsimp simp: objBits_def cong: option.case_cong)
     apply (erule (1) ps_clear_lookupAround2)
       apply simp
      apply (erule is_aligned_no_overflow)
     apply (simp add: objBits_simps archObjSize_def word_bits_def)
    apply simp
    apply (clarsimp simp: in_monad loadObject_default_def
      projectKOs and_not_mask_twice)
    apply (simp add: bind_assoc exec_gets)
    apply (clarsimp simp: pte_at_def obj_at_def)
    apply (clarsimp split:ARM_A.pte.splits)
    apply (intro conjI impI)
  -- "master_pde = InvaliatePTE"
      apply (clarsimp simp add: a_type_def return_def get_pt_def
                  bind_def get_pte_def get_object_def gets_def get_def
                  split: if_split_asm Structures_A.kernel_object.splits arch_kernel_obj.splits)
      apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
      apply (clarsimp simp: in_magnitude_check objBits_simps archObjSize_def pageBits_def pteBits_def)
      apply (clarsimp simp:state_relation_def)
      apply (frule_tac x = "(ucast (p && mask pt_bits >> 2))" in pte_relation_alignedD)
        apply assumption
       apply (simp add:mask_pt_bits_inner_beauty)
      apply (clarsimp simp:pte_relation_aligned_def
        split:if_splits ARM_H.pte.splits)
      apply (drule_tac p' = "p && ~~ mask 6" in valid_duplicates'_D[rotated])
         apply (simp add:is_aligned_weaken[where y = 2] is_aligned_neg_mask)
        apply (clarsimp simp: vs_ptr_align_def)
       apply (simp add:and_not_mask_twice)
      apply (frule_tac x = "(ucast ((p && ~~ mask 6) && mask pt_bits >> 2))" in pte_relation_alignedD)
        apply assumption
       apply (simp add:expand)
       apply (subst mask_pt_bits_inner_beauty)
        apply (simp add:is_aligned_neg_mask)
       apply assumption
      apply (clarsimp simp: pte_relation_aligned_def
                 is_aligned_mask[where 'a=32, symmetric])
  -- "master_pde = LargePagePTE"
     apply (clarsimp simp add: a_type_def return_def get_pt_def
       bind_def get_pte_def get_object_def gets_def get_def
       split: if_split_asm Structures_A.kernel_object.splits arch_kernel_obj.splits)
     apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
     apply (clarsimp simp: in_magnitude_check objBits_simps archObjSize_def pageBits_def pteBits_def)
     apply (clarsimp simp:state_relation_def)
     apply (drule_tac s = a and s' = b and p = "p && ~~ mask 6"
      in aligned_distinct_relation_pte_atI'[rotated -1])
        apply (clarsimp simp:pte_at_def obj_at_def
          and_not_mask_twice a_type_simps is_aligned_neg_mask)
       apply simp
      apply simp
     apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
     apply (case_tac ko; simp)
     apply (rename_tac arch_kernel_object)
     apply (case_tac arch_kernel_object, simp_all add: projectKOs)[1]
     apply clarsimp
     apply (frule_tac x = "(ucast ((p && ~~ mask 6 )&& mask pt_bits >> 2))" in pte_relation_alignedD)
       apply assumption
      apply (simp add: expand)
      apply (subst mask_pt_bits_inner_beauty)
       apply (simp add:is_aligned_neg_mask)
      apply assumption
     apply (rename_tac pte)
     apply (case_tac pte)
       apply (simp_all add:pte_relation_aligned_def is_aligned_mask[symmetric])
     apply (drule_tac p = "p && ~~ mask 6" and p' = p  in valid_duplicates'_D)
        apply assumption
       apply simp
      apply (clarsimp simp: vs_ptr_align_def and_not_mask_twice)
     apply (clarsimp simp: if_bool_eq_disj)
  -- "master_pde = SmallPagePTE"
    apply (clarsimp simp add: a_type_def return_def get_pt_def
               bind_def get_pte_def get_object_def gets_def get_def
            split: if_split_asm Structures_A.kernel_object.splits
                   arch_kernel_obj.splits)
   apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
   apply (clarsimp simp: in_magnitude_check objBits_simps
                         archObjSize_def pageBits_def pteBits_def)
   apply (clarsimp simp:state_relation_def)
   apply (frule_tac x = "(ucast (p && mask pt_bits >> 2))"
                 in pte_relation_alignedD)
     apply assumption
    apply (simp add:mask_pt_bits_inner_beauty)
   apply (clarsimp simp:pte_relation_aligned_def
     split:if_splits ARM_H.pte.splits)
   apply (drule_tac p' = "p && ~~ mask 6" in valid_duplicates'_D[rotated])
      apply (simp add:is_aligned_weaken[where y = 2] is_aligned_neg_mask)
     apply (clarsimp simp: vs_ptr_align_def)
    apply (simp add:and_not_mask_twice)
   apply (drule_tac x = "(ucast ((p && ~~ mask 6) && mask pt_bits >> 2))"
                 in pte_relation_alignedD)
     apply assumption
    apply (simp add: expand)
    apply (subst mask_pt_bits_inner_beauty)
     apply (simp add:is_aligned_neg_mask)
    apply assumption
   apply (clarsimp simp: pte_relation_aligned_def
                         is_aligned_mask[where 'a=32, symmetric])
   done
  qed

lemma get_pte_corres':
  "corres (pte_relation_aligned (p >> 2)) (pte_at p)
     (pspace_aligned' and pspace_distinct')
     (get_pte p) (getObject p)"
  apply (rule stronger_corres_guard_imp,
         rule get_pte_corres)
   apply auto[1]
  apply clarsimp
  apply (rule aligned_distinct_relation_pte_atI')
   apply (simp add:state_relation_def)+
  done

lemma get_master_pte_corres':
  "corres pte_relation' (pte_at p)
     ((\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
      pspace_aligned' and pspace_distinct')
     (get_master_pte p) (getObject p)"
  apply (rule stronger_corres_guard_imp,
         rule get_master_pte_corres)
   apply auto
  done

(* FIXME: move *)
lemma pd_slot_eq:
  "((p::word32) && ~~ mask pd_bits) + (ucast x << 2) = p \<Longrightarrow>
    (x::12 word) = ucast (p && mask pd_bits >> 2)"
  apply (clarsimp simp:mask_def pd_bits_def pageBits_def)
  apply word_bitwise
  apply clarsimp
  done

(* FIXME: move *)
lemma pt_slot_eq:
  "((p::word32) && ~~ mask pt_bits) + (ucast x << 2) = p \<Longrightarrow>
    (x::word8) = ucast (p && mask pt_bits >> 2)"
  apply (clarsimp simp:mask_def pt_bits_def pageBits_def)
  apply word_bitwise
  apply clarsimp
  done

-- "set_other_obj_corres unfortunately doesn't work here"
lemma set_pd_corres [@lift_corres_args, corres]:
  "pde_relation_aligned (p>>2) pde pde' \<Longrightarrow>
         corres dc  (ko_at (ArchObj (PageDirectory pd)) (p && ~~ mask pd_bits) 
                     and pspace_aligned and valid_etcbs) 
                    (pde_at' p)
          (set_pd (p && ~~ mask pd_bits) (pd(ucast (p && mask pd_bits >> 2) := pde)))
          (setObject p pde')"
  apply (simp add: set_pd_def get_object_def bind_assoc)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
    apply simp
   apply (clarsimp simp: obj_at'_def ko_wp_at'_def typ_at'_def lookupAround2_known1 projectKOs)
   apply (case_tac ko, simp_all)[1]
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object, simp_all add: projectKOs)[1]
   apply (simp add: objBits_simps archObjSize_def word_bits_def)
  apply (clarsimp simp: setObject_def in_monad split_def updateObject_default_def projectKOs)
  apply (simp add: in_magnitude_check objBits_simps archObjSize_def pageBits_def pdeBits_def)
  apply (clarsimp simp: obj_at_def exec_gets)
  apply (clarsimp simp: set_object_def bind_assoc exec_get)
  apply (clarsimp simp: put_def)
  apply (clarsimp simp: state_relation_def mask_pd_bits_inner_beauty)
  apply (rule conjI)
   apply (clarsimp simp: pspace_relation_def split del: if_split)
   apply (rule conjI)
    apply (subst pspace_dom_update, assumption)
     apply (simp add: a_type_def)
    apply (auto simp: dom_def)[1]
   apply (rule conjI)
    apply (drule bspec, blast)
    apply clarsimp
    apply (drule_tac x = x in spec)
    apply (clarsimp simp: pde_relation_def mask_pd_bits_inner_beauty pde_relation_aligned_simp
      dest!: more_pd_inner_beauty)
   apply (rule ballI)
   apply (drule (1) bspec)
   apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp: pde_relation_def mask_pd_bits_inner_beauty pde_relation_aligned_simp
      dest!: more_pd_inner_beauty)
   apply clarsimp
   apply (drule bspec, assumption)
   apply clarsimp
   apply (erule (1) obj_relation_cutsE)
       apply simp
      apply simp
     apply clarsimp
     apply (frule (1) pspace_alignedD)
     apply (drule_tac p=x in pspace_alignedD, assumption)
     apply simp
     apply (drule mask_alignment_ugliness)
        apply (simp add: pd_bits_def pageBits_def)
       apply (simp add: pd_bits_def pageBits_def)
      apply clarsimp
      apply (clarsimp simp: nth_ucast nth_shiftl)
      apply (drule test_bit_size)
      apply (clarsimp simp: word_size pd_bits_def pageBits_def)
      apply arith
     apply (simp split: if_split_asm)
    apply (simp split: if_split_asm)
   apply (simp add: other_obj_relation_def
               split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (rule conjI)
   apply (clarsimp simp: ekheap_relation_def pspace_relation_def)
   apply (drule(1) ekheap_kheap_dom)
   apply clarsimp
   apply (drule_tac x=p in bspec, erule domI)
   apply (simp add: other_obj_relation_def
           split: Structures_A.kernel_object.splits)
  apply (rule conjI)
   apply (clarsimp simp add: ghost_relation_def)
   apply (erule_tac x="p && ~~ mask pd_bits" in allE)+
   apply fastforce
  apply (simp add: map_to_ctes_upd_other)
  apply (simp add: fun_upd_def)
  apply (simp add: caps_of_state_after_update obj_at_def swp_cte_at_caps_of)
  done


lemma set_pt_corres [@lift_corres_args, corres]:
  "pte_relation_aligned (p >> 2) pte pte' \<Longrightarrow>
         corres dc  (ko_at (ArchObj (PageTable pt)) (p && ~~ mask pt_bits) 
                     and pspace_aligned and valid_etcbs) 
                    (pte_at' p)
          (set_pt (p && ~~ mask pt_bits) (pt(ucast (p && mask pt_bits >> 2) := pte)))
          (setObject p pte')"
  apply (simp add: set_pt_def get_object_def bind_assoc)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
    apply simp
   apply (clarsimp simp: obj_at'_def ko_wp_at'_def typ_at'_def lookupAround2_known1 projectKOs)
   apply (case_tac ko, simp_all)[1]
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object, simp_all add: projectKOs)[1]
   apply (simp add: objBits_simps archObjSize_def word_bits_def)
  apply (clarsimp simp: setObject_def in_monad split_def updateObject_default_def projectKOs)
  apply (simp add: in_magnitude_check objBits_simps archObjSize_def pageBits_def pteBits_def)
  apply (clarsimp simp: obj_at_def exec_gets)
  apply (clarsimp simp: set_object_def bind_assoc exec_get)
  apply (clarsimp simp: put_def)
  apply (clarsimp simp: state_relation_def mask_pt_bits_inner_beauty)
  apply (rule conjI)
   apply (clarsimp simp: pspace_relation_def split del: if_split)
   apply (rule conjI)
    apply (subst pspace_dom_update, assumption)
     apply (simp add: a_type_def)
    apply (auto simp: dom_def)[1]
   apply (rule conjI)
    apply (drule bspec, blast)
    apply (clarsimp simp: pte_relation_def mask_pt_bits_inner_beauty pte_relation_aligned_simp
      dest!: more_pt_inner_beauty)
   apply (rule ballI)
   apply (drule (1) bspec)
   apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp: pte_relation_def mask_pt_bits_inner_beauty pte_relation_aligned_simp
      dest!: more_pt_inner_beauty)
   apply clarsimp
   apply (drule bspec, assumption)
   apply clarsimp
   apply (erule (1) obj_relation_cutsE)
       apply simp
      apply clarsimp
      apply (frule (1) pspace_alignedD)
      apply (drule_tac p=x in pspace_alignedD, assumption)
      apply simp
      apply (drule mask_alignment_ugliness)
         apply (simp add: pt_bits_def pageBits_def)
        apply (simp add: pt_bits_def pageBits_def)
       apply clarsimp
       apply (clarsimp simp: nth_ucast nth_shiftl)
       apply (drule test_bit_size)
       apply (clarsimp simp: word_size pt_bits_def pageBits_def)
       apply arith
      apply simp
     apply (simp split: if_split_asm)
    apply (simp split: if_split_asm)
   apply (simp add: other_obj_relation_def
               split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (rule conjI)
   apply (clarsimp simp: ekheap_relation_def pspace_relation_def)
   apply (drule(1) ekheap_kheap_dom)
   apply clarsimp
   apply (drule_tac x=p in bspec, erule domI)
   apply (simp add: other_obj_relation_def
           split: Structures_A.kernel_object.splits)
  apply (rule conjI)
   apply (clarsimp simp add: ghost_relation_def)
   apply (erule_tac x="p && ~~ mask pt_bits" in allE)+
   apply fastforce
  apply (simp add: map_to_ctes_upd_other)
  apply (simp add: fun_upd_def)
  apply (simp add: caps_of_state_after_update obj_at_def swp_cte_at_caps_of)
  done
lemma store_pde_corres [@lift_corres_args, corres]:
  "pde_relation_aligned (p >> 2) pde pde' \<Longrightarrow> 
  corres dc (pde_at p and pspace_aligned and valid_etcbs) (pde_at' p) (store_pde p pde) (storePDE p pde')"
  apply (simp add: store_pde_def storePDE_def)
  apply (rule corres_symb_exec_l)
     apply (erule set_pd_corres[OF _ refl])
    apply (clarsimp simp: exs_valid_def get_pd_def get_object_def exec_gets bind_assoc
                          obj_at_def pde_at_def)
    apply (clarsimp simp: a_type_def return_def
                    split: Structures_A.kernel_object.splits arch_kernel_obj.splits if_split_asm)
   apply wp
   apply clarsimp
  apply (clarsimp simp: get_pd_def obj_at_def no_fail_def pde_at_def
                        get_object_def bind_assoc exec_gets)
  apply (clarsimp simp: a_type_def return_def
                  split: Structures_A.kernel_object.splits arch_kernel_obj.splits if_split_asm)
  done

lemma store_pde_corres':
  "pde_relation_aligned (p >> 2) pde pde' \<Longrightarrow>
  corres dc
     (pde_at p and pspace_aligned and valid_etcbs) (pspace_aligned' and pspace_distinct')
     (store_pde p pde) (storePDE p pde')"
  apply (rule stronger_corres_guard_imp, rule store_pde_corres)
   apply auto
  done

lemma store_pte_corres [@lift_corres_args, corres]:
  "pte_relation_aligned (p>>2) pte pte' \<Longrightarrow> 
  corres dc (pte_at p and pspace_aligned and valid_etcbs) (pte_at' p) (store_pte p pte) (storePTE p pte')"
  apply (simp add: store_pte_def storePTE_def)
  apply (rule corres_symb_exec_l)
     apply (erule set_pt_corres[OF _ refl])
    apply (clarsimp simp: exs_valid_def get_pt_def get_object_def
                          exec_gets bind_assoc obj_at_def pte_at_def)
    apply (clarsimp simp: a_type_def return_def
                    split: Structures_A.kernel_object.splits arch_kernel_obj.splits if_split_asm)
   apply wp
   apply clarsimp
  apply (clarsimp simp: get_pt_def obj_at_def pte_at_def no_fail_def
                        get_object_def bind_assoc exec_gets)
  apply (clarsimp simp: a_type_def return_def
                  split: Structures_A.kernel_object.splits arch_kernel_obj.splits if_split_asm)
  done

lemma store_pte_corres':
  "pte_relation_aligned (p >> 2) pte pte' \<Longrightarrow>
  corres dc (pte_at p and pspace_aligned and valid_etcbs)
            (pspace_aligned' and pspace_distinct')
            (store_pte p pte) (storePTE p pte')"
  apply (rule stronger_corres_guard_imp, rule store_pte_corres)
   apply auto
  done

lemma lookup_pd_slot_corres [simp]:
  "lookupPDSlot pd vptr = lookup_pd_slot pd vptr"
  by (simp add: lookupPDSlot_def lookup_pd_slot_def pageBits_def ptBits_def pdeBits_def)

defs checkPDAt_def:
  "checkPDAt pd \<equiv> stateAssert (page_directory_at' pd) []"

defs checkPTAt_def:
  "checkPTAt pt \<equiv> stateAssert (page_table_at' pt) []"

lemma pte_relation_must_pte:
  "pte_relation m (ArchObj (PageTable pt)) ko \<Longrightarrow> \<exists>pte. ko = (KOArch (KOPTE pte))"
  apply (case_tac ko)
   apply (simp_all add:pte_relation_def)
  apply clarsimp
  done

lemma pde_relation_must_pde:
  "pde_relation m (ArchObj (PageDirectory pd)) ko \<Longrightarrow> \<exists>pde. ko = (KOArch (KOPDE pde))"
  apply (case_tac ko)
   apply (simp_all add:pde_relation_def)
  apply clarsimp
  done

lemma page_table_at_state_relation:
  "\<lbrakk>page_table_at (ptrFromPAddr ptr) s; pspace_aligned s;
     (s, sa) \<in> state_relation;pspace_distinct' sa\<rbrakk>
  \<Longrightarrow> page_table_at' (ptrFromPAddr ptr) sa"
  apply (clarsimp simp:page_table_at'_def state_relation_def
    obj_at_def)
  apply (clarsimp simp:pspace_relation_def)
  apply (drule bspec)
   apply fastforce
  apply clarsimp
  apply (frule(1) pspace_alignedD)
   apply (simp add:ptrFromPAddr_def ptBits_def pageBits_def pteBits_def)
  apply clarsimp
  apply (drule_tac x = "ucast y" in spec)
  apply (drule sym[where s = "pspace_dom (kheap s)"])
  apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
  apply (subgoal_tac "(ptr + physMappingOffset + (y << 2)) \<in> dom (ksPSpace sa)")
   prefer 2
   apply (clarsimp simp: pspace_dom_def)
   apply (rule_tac x = "ptr + physMappingOffset" in bexI[where A = "dom (kheap s)"])
    apply (simp add:image_def)
    apply (rule_tac x = "ucast y" in exI)
    apply (simp add:ucast_ucast_len)
   apply fastforce
  apply (thin_tac "dom a = b" for a b)
  apply (frule(1) pspace_alignedD)
  apply (clarsimp simp:ucast_ucast_len
    split:if_splits)
  apply (drule pte_relation_must_pte)
  apply (drule(1) pspace_distinctD')
  apply (clarsimp simp:objBits_simps archObjSize_def)
  apply (rule is_aligned_weaken)
   apply (erule aligned_add_aligned)
    apply (rule is_aligned_shiftl_self)
   apply simp
  apply (simp add: pteBits_def)
  done

lemma page_directory_at_state_relation:
  "\<lbrakk>page_directory_at ptr s; pspace_aligned s;
     (s, sa) \<in> state_relation;pspace_distinct' sa\<rbrakk>
  \<Longrightarrow> page_directory_at' ptr sa"
  apply (clarsimp simp:page_directory_at'_def state_relation_def obj_at_def)
  apply (clarsimp simp:pspace_relation_def)
  apply (drule bspec)
   apply fastforce
  apply clarsimp
  apply (frule(1) pspace_alignedD)
   apply (simp add: pdBits_def pageBits_def pdeBits_def)
  apply clarsimp
  apply (drule_tac x = "ucast y" in spec)
  apply (drule sym[where s = "pspace_dom (kheap s)"])
  apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
  apply (subgoal_tac "(ptr + (y << 2)) \<in> dom (ksPSpace sa)")
   prefer 2
   apply (clarsimp simp: pspace_dom_def)
   apply (rule_tac x = "ptr" in bexI[where A = "dom (kheap s)"])
    apply (simp add: image_def)
    apply (rule_tac x = "ucast y" in exI)
    apply (simp add:ucast_ucast_len)
   apply fastforce
  apply (thin_tac "dom a = b" for a b)
  apply (frule(1) pspace_alignedD)
  apply (clarsimp simp:ucast_ucast_len split:if_splits)
  apply (drule pde_relation_must_pde)
  apply (drule(1) pspace_distinctD')
  apply (clarsimp simp:objBits_simps archObjSize_def)
  apply (rule is_aligned_weaken)
   apply (erule aligned_add_aligned)
    apply (rule is_aligned_shiftl_self)
   apply simp
  apply (simp add: pdeBits_def)
  done

lemma getPDE_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' (ko::pde) p s \<longrightarrow> Q ko s\<rbrace> getObject p \<lbrace>Q\<rbrace>"
  by (clarsimp simp: getObject_def split_def loadObject_default_def
                     archObjSize_def in_magnitude_check pdeBits_def
                     projectKOs in_monad valid_def obj_at'_def objBits_simps)

lemma getPTE_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' (ko::pte) p s \<longrightarrow> Q ko s\<rbrace> getObject p \<lbrace>Q\<rbrace>"
  by (clarsimp simp: getObject_def split_def loadObject_default_def
                     archObjSize_def in_magnitude_check pteBits_def
                     projectKOs in_monad valid_def obj_at'_def objBits_simps)

lemmas get_pde_wp_valid = hoare_add_post'[OF get_pde_valid get_pde_wp]

lemma page_table_at_lift:
  "\<forall>s s'. (s, s') \<in> state_relation \<longrightarrow> (ptrFromPAddr ptr) = ptr' \<longrightarrow>
  (pspace_aligned s \<and> valid_pde (ARM_A.PageTablePDE ptr x z) s) \<longrightarrow>
  pspace_distinct' s' \<longrightarrow> page_table_at' ptr' s'"
  by (fastforce intro!: page_table_at_state_relation)

lemmas checkPTAt_corres [corresK] =
  corres_stateAssert_implied_frame[OF page_table_at_lift, folded checkPTAt_def]

lemma lookup_pt_slot_corres [@lift_corres_args, corres]:
  "corres (lfr \<oplus> op =)
          (pde_at (lookup_pd_slot pd vptr) and pspace_aligned and valid_vspace_objs
          and (\<exists>\<rhd> (lookup_pd_slot pd vptr && ~~ mask pd_bits)) and
          K (is_aligned pd pd_bits \<and> vptr < kernel_base
          \<and> ucast (lookup_pd_slot pd vptr && mask pd_bits >> 2) \<notin> kernel_mapping_slots))
          (pspace_aligned' and pspace_distinct')
          (lookup_pt_slot pd vptr) (lookupPTSlot pd vptr)"
  unfolding lookup_pt_slot_def lookupPTSlot_def lookupPTSlotFromPT_def
  apply (corressimp simp: pde_relation_aligned_def lookup_failure_map_def
                          ptBits_def pdeBits_def pageBits_def pteBits_def mask_def
                      wp: get_pde_wp_valid getPDE_wp corres_rv_defer_left)
  by (auto simp: lookup_failure_map_def obj_at_def)

declare in_set_zip_refl[simp]

crunch typ_at' [wp]: storePDE "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps mapM_x_wp' simp: crunch_simps)

crunch typ_at' [wp]: storePTE "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps mapM_x_wp' simp: crunch_simps)

lemmas storePDE_typ_ats[wp] = typ_at_lifts [OF storePDE_typ_at']
lemmas storePTE_typ_ats[wp] = typ_at_lifts [OF storePTE_typ_at']

lemma setObject_asid_typ_at' [wp]:
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> setObject p' (v::asidpool) \<lbrace>\<lambda>_ s. P (typ_at' T p s)\<rbrace>"
  by (wp setObject_typ_at')

lemmas setObject_asid_typ_ats' [wp] = typ_at_lifts [OF setObject_asid_typ_at']

lemma getObject_pte_inv[wp]:
  "\<lbrace>P\<rbrace> getObject p \<lbrace>\<lambda>rv :: pte. P\<rbrace>"
  by (simp add: getObject_inv loadObject_default_inv)

lemma getObject_pde_inv[wp]:
  "\<lbrace>P\<rbrace> getObject p \<lbrace>\<lambda>rv :: pde. P\<rbrace>"
  by (simp add: getObject_inv loadObject_default_inv)

crunch typ_at'[wp]: copyGlobalMappings "\<lambda>s. P (typ_at' T p s)"
  (wp: mapM_x_wp' ignore: forM_x getObject)

lemmas copyGlobalMappings_typ_ats[wp] = typ_at_lifts [OF copyGlobalMappings_typ_at']

lemma align_entry_add_cong:
  "\<lbrakk>is_aligned (pd::word32) 6; is_aligned pd' 6\<rbrakk>
  \<Longrightarrow> is_aligned (pd + x >> 2) (pde_align' y)  =
      is_aligned (pd' + x >> 2) (pde_align' y) "
  apply (clarsimp simp: pde_align'_def is_aligned_mask mask_def
                 split: ARM_H.pde.splits)
  apply word_bitwise
  apply auto
  done

lemma arm_global_pd_corres [corres]:
  "corres op = (\<lambda>_. True) (\<lambda>_. True)
     (gets (arm_global_pd \<circ> arch_state)) (gets (armKSGlobalPD \<circ> ksArchState))"
 by (clarsimp simp: state_relation_def arch_state_relation_def)



lemma copy_global_mappings_corres [@lift_corres_args, corres]:
  "corres dc (page_directory_at pd and pspace_aligned and valid_arch_state and valid_etcbs)
             (page_directory_at' pd and valid_arch_state')
          (copy_global_mappings pd) (copyGlobalMappings pd)" (is "corres _ ?apre _ _ _")
  unfolding copy_global_mappings_def copyGlobalMappings_def pd_bits_def pdBits_def objBits_simps
            archObjSize_def kernel_base_def ARM.kernelBase_def ARM_H.kernelBase_def
  apply corressimp
     apply (rule_tac P="page_directory_at global_pd
                        and (\<lambda>_. is_aligned global_pd 6 \<and> is_aligned pd 6) and ?apre" and
                    P'="page_directory_at' globalPD and page_directory_at' pd"
              in corresK_mapM_x[OF order_refl])
        apply (corressimp wp: get_pde_wp getPDE_wp corres_rv_wp_left)
        subgoal for globalPD
          by (auto intro!: page_directory_pde_atI page_directory_pde_atI'
                     simp: pde_relation_aligned_def
                     dest: align_entry_add_cong[of globalPD])
  apply wpsimp+
  apply (clarsimp simp: valid_arch_state_def obj_at_def dest!:pspace_alignedD)
  by (auto intro: is_aligned_weaken[of _ 14] simp: valid_arch_state'_def)


lemma arch_cap_rights_update:
  "acap_relation c c' \<Longrightarrow>
   cap_relation (cap.ArchObjectCap (acap_rights_update (acap_rights c \<inter> msk) c))
                 (Arch.maskCapRights (rights_mask_map msk) c')"
  apply (cases c, simp_all add: ARM_H.maskCapRights_def
                                acap_rights_update_def Let_def isCap_simps)
  apply (simp add: maskVMRights_def vmrights_map_def rights_mask_map_def
                   validate_vm_rights_def vm_read_write_def vm_read_only_def
                   vm_kernel_only_def )
  done

lemma arch_deriveCap_inv:
  "\<lbrace>P\<rbrace> Arch.deriveCap arch_cap u \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp      add: ARM_H.deriveCap_def
                  cong: if_cong
             split del: if_split)
  apply (rule hoare_pre, wp undefined_valid)
  apply (cases u, simp_all add: isCap_defs)
  done

lemma arch_deriveCap_valid:
  "\<lbrace>valid_cap' (ArchObjectCap arch_cap)\<rbrace>
     Arch.deriveCap u arch_cap
   \<lbrace>\<lambda>rv. valid_cap' (ArchObjectCap rv)\<rbrace>,-"
  apply (simp      add: ARM_H.deriveCap_def
                  cong: if_cong
             split del: if_split)
  apply (rule hoare_pre, wp undefined_validE_R)
  apply (cases arch_cap, simp_all add: isCap_defs)
  apply (simp add: valid_cap'_def capAligned_def
                   capUntypedPtr_def ARM_H.capUntypedPtr_def)
  done

lemma arch_derive_corres [corres]:
 "cap_relation (cap.ArchObjectCap c) (ArchObjectCap c') \<Longrightarrow>
  corres (ser \<oplus> (\<lambda>c c'. cap_relation (cap.ArchObjectCap c) (ArchObjectCap c')))
         \<top> \<top>
         (arch_derive_cap c)
         (Arch.deriveCap slot c')"
  unfolding arch_derive_cap_def ARM_H.deriveCap_def Let_def
  apply (cases c, simp_all add: isCap_simps split: option.splits split del: if_split)
      apply (clarify?, rule corres_noopE; wpsimp)+
  done

definition
  "vmattributes_map \<equiv> \<lambda>R. VMAttributes (PageCacheable \<in> R) (ParityEnabled \<in> R) (XNever \<in> R)"

definition
  mapping_map :: "ARM_A.pte \<times> word32 list + ARM_A.pde \<times> word32 list \<Rightarrow>
                  ARM_H.pte \<times> word32 list + ARM_H.pde \<times> word32 list \<Rightarrow> bool"
where
  "mapping_map \<equiv> pte_relation' \<otimes> (op =) \<oplus> pde_relation' \<otimes> (op =)"

lemma create_mapping_entries_corres [corres]:
  "\<lbrakk> vm_rights' = vmrights_map vm_rights;
     attrib' = vmattributes_map attrib \<rbrakk>
  \<Longrightarrow> corres (ser \<oplus> mapping_map)
          (\<lambda>s. (pgsz = ARMSmallPage \<or> pgsz = ARMLargePage \<longrightarrow> pde_at (lookup_pd_slot pd vptr) s)
           \<and> (is_aligned pd pd_bits \<and> vmsz_aligned vptr pgsz \<and> vptr < kernel_base \<and> vm_rights \<in> valid_vm_rights)
           \<and> valid_vspace_objs s \<and> pspace_aligned s \<and> (\<exists>\<rhd> (lookup_pd_slot pd vptr && ~~ mask pd_bits)) s)
          (pspace_aligned' and pspace_distinct')
          (create_mapping_entries base vptr pgsz vm_rights attrib pd) 
          (createMappingEntries base' vptr' pgsz' vm_rights' attrib' pd')"
  unfolding createMappingEntries_def mapping_map_def
  apply (cases pgsz; corressimp simp: vmattributes_map_def less_kernel_base_mapping_slots)
    apply (rule corres_rv_defer_left)
   apply (auto dest: less_kernel_base_mapping_slots
               simp: vmattributes_map_def
                     largePagePTEOffsets_def
                     largePagePTE_offsets_def
                     superSectionPDEOffsets_def
                     superSectionPDE_offsets_def
                     pteBits_def pdeBits_def)
  done

lemma pte_relation'_Invalid_inv [simp]:
  "pte_relation' x ARM_H.pte.InvalidPTE = (x = ARM_A.pte.InvalidPTE)"
  by (cases x) auto

definition
  "valid_slots' m \<equiv> case m of
    Inl (pte, xs) \<Rightarrow> \<lambda>s. valid_pte' pte s
  | Inr (pde, xs) \<Rightarrow> \<lambda>s. valid_pde' pde s"

lemma valid_slots_typ_at':
  assumes x: "\<And>T p. \<lbrace>typ_at' T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at' T p\<rbrace>"
  shows "\<lbrace>valid_slots' m\<rbrace> f \<lbrace>\<lambda>rv. valid_slots' m\<rbrace>"
  unfolding valid_slots'_def
  apply (cases m)
   apply (case_tac a)
   apply simp
   apply (wp x valid_pte_lift')
  apply (case_tac b)
  apply simp
  apply (wp x valid_pde_lift')
  done

lemma createMappingEntries_valid_slots' [wp]:
  "\<lbrace>valid_objs' and
    K (vmsz_aligned' base sz \<and> vmsz_aligned' vptr sz \<and> ptrFromPAddr base \<noteq> 0) \<rbrace>
  createMappingEntries base vptr sz vm_rights attrib pd
  \<lbrace>\<lambda>m. valid_slots' m\<rbrace>, -"
  apply (simp add: createMappingEntries_def)
  apply (rule hoare_pre)
   apply (wp|wpc|simp add: valid_slots'_def valid_mapping'_def)+
  apply (simp add: vmsz_aligned'_def)
  apply auto
  done

lemma ensure_safe_mapping_corres [corres]:
  "mapping_map m m' \<Longrightarrow>
  corres (ser \<oplus> dc) (valid_mapping_entries m)
                    (pspace_aligned' and pspace_distinct'
                    and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
                    (ensure_safe_mapping m) (ensureSafeMapping m')"
  unfolding mapping_map_def ensureSafeMapping_def
  apply (cases m; cases m'; simp;
         match premises in "(_ \<otimes> op =) p p'" for p p' \<Rightarrow> \<open>cases "fst p"; cases "fst p'"\<close>; clarsimp)
        by (corressimp corresK: mapME_x_corresK_inv
                           wp: get_master_pte_wp get_master_pde_wp getPTE_wp getPDE_wp;
            auto simp add: valid_mapping_entries_def)+

lemma asidHighBitsOf [simp]:
  "asidHighBitsOf asid = ucast (asid_high_bits_of asid)"
  apply (simp add: asidHighBitsOf_def asid_high_bits_of_def asidHighBits_def)
  apply (rule word_eqI)
  apply (simp add: word_size nth_ucast)
  done


lemma page_directory_at_lift:
  "corres_inst_eq ptr ptr' \<Longrightarrow> \<forall>s s'. (s, s') \<in> state_relation \<longrightarrow> True \<longrightarrow>
  (pspace_aligned s \<and> page_directory_at ptr s) \<longrightarrow>
  pspace_distinct' s' \<longrightarrow> page_directory_at' ptr' s'"
  by (fastforce simp: corres_inst_eq_def intro!: page_directory_at_state_relation )

lemmas checkPDAt_corres =
  corres_stateAssert_implied_frame[OF page_directory_at_lift, folded checkPDAt_def]

lemma getASID_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' (ko::asidpool) p s \<longrightarrow> Q ko s\<rbrace> getObject p \<lbrace>Q\<rbrace>"
  by (clarsimp simp: getObject_def split_def loadObject_default_def
                     archObjSize_def in_magnitude_check pageBits_def
                     projectKOs in_monad valid_def obj_at'_def objBits_simps)

lemma ko_at_typ_at_asidpool:
  "ko_at (ArchObj (arch_kernel_obj.ASIDPool pool)) x s \<Longrightarrow> typ_at (AArch AASIDPool) x s"
  by (clarsimp simp: obj_at_def a_type_simps)





lemma find_pd_for_asid_corres [corres]:
  "asid = asid' \<Longrightarrow> corres (lfr \<oplus> op =) ((\<lambda>s. valid_arch_state s \<or> vspace_at_asid asid pd s)
                           and valid_arch_objs and pspace_aligned
                           and K (0 < asid \<and> asid \<le> mask asidBits))
                       (pspace_aligned' and pspace_distinct' and no_0_obj')
                       (find_pd_for_asid asid) (findPDForASID asid')"
  apply (simp add: find_pd_for_asid_def findPDForASID_def liftME_def bindE_assoc)
  apply (corressimp simp: liftE_bindE assertE_assert mask_asid_low_bits_ucast_ucast
                          lookup_failure_map_def
                      wp: getPDE_wp getASID_wp
                  search: checkPDAt_corres corres_gets_asid)
  subgoal premises prems for s s'
  apply (intro allI impI conjI)
      subgoal asid_pool_at for x
       apply (insert prems)
       apply (elim conjE disjE)
       apply (fastforce dest: valid_asid_tableD)
       apply (clarsimp simp: vspace_at_asid_def valid_arch_objs_def)
       apply (clarsimp simp: vs_asid_refs_def graph_of_def elim!: vs_lookupE)
        apply (erule rtranclE)
        subgoal by simp
       apply (simp add: arm_asid_table_related)
       apply (clarsimp dest!: vs_lookup1D)
        apply (erule rtranclE)
        apply (clarsimp simp: vs_refs_def graph_of_def obj_at_def a_type_def
                       split: Structures_A.kernel_object.splits
                              arch_kernel_obj.splits)
        apply (clarsimp dest!: vs_lookup1D)
         apply (erule rtranclE)
        apply (fastforce dest!: vs_lookup1D)
        by (clarsimp dest!: vs_lookup1D)
     subgoal pd_at for x pool xa
      apply (insert prems)
       apply (rule valid_arch_obj_elims)
       apply (rule valid_arch_objsD)
        apply (rule vs_lookupI)
        apply (rule vs_asid_refsI)
       apply fastforce
      apply (rule rtrancl_refl)
      by (simp add: ranI)+
    apply (insert prems)
    apply (fastforce simp add: asidRange_def mask_2pm1[symmetric])
  subgoal for x by (insert asid_pool_at[of x], auto simp: arm_asid_table_related)
  subgoal for x ko
   apply (cases ko; simp)
   apply (frule arm_asid_table_related[where s'=s', simplified o_def])
   apply (cut_tac asid_pool_at[of x, simplified obj_at_def])
     apply clarsimp
     apply (frule pspace_relation_absD, fastforce)
     apply (clarsimp simp: other_obj_relation_def obj_at'_def projectKOs asid_pool_relation_def)
        apply (cut_tac pd_at[of _ _ 0]; assumption?)
        apply (drule(1) no_0_obj'_abstract)
        by (auto simp add: obj_at_def inv_def o_def)
  done
  done

lemma find_pd_for_asid_corres':
  "corres (lfr \<oplus> op =) (vspace_at_asid asid pd and valid_arch_objs
                           and pspace_aligned and  K (0 < asid \<and> asid \<le> mask asidBits))
                       (pspace_aligned' and pspace_distinct' and no_0_obj')
                       (find_pd_for_asid asid) (findPDForASID asid)"
  apply (rule corres_guard_imp, rule find_pd_for_asid_corres)
   apply fastforce+
  done

lemma setObject_arch:
  assumes X: "\<And>p q n ko. \<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> updateObject val p q n ko \<lbrace>\<lambda>rv s. P (ksArchState s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> setObject t val \<lbrace>\<lambda>rv s. P (ksArchState s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp X | simp)+
  done

lemma setObject_ASID_arch [wp]:
  "\<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> setObject p (v::asidpool) \<lbrace>\<lambda>_ s. P (ksArchState s)\<rbrace>"
  apply (rule setObject_arch)
  apply (simp add: updateObject_default_def)
  apply wp
  apply simp
  done

lemma setObject_PDE_arch [wp]:
  "\<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> setObject p (v::pde) \<lbrace>\<lambda>_ s. P (ksArchState s)\<rbrace>"
  apply (rule setObject_arch)
  apply (simp add: updateObject_default_def)
  apply wp
  apply simp
  done

lemma setObject_PTE_arch [wp]:
  "\<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> setObject p (v::pte) \<lbrace>\<lambda>_ s. P (ksArchState s)\<rbrace>"
  apply (rule setObject_arch)
  apply (simp add: updateObject_default_def)
  apply wp
  apply simp
  done

lemma setObject_ASID_valid_arch [wp]:
  "\<lbrace>valid_arch_state'\<rbrace> setObject p (v::asidpool) \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  by (rule valid_arch_state_lift'; wp)

lemma setObject_PDE_valid_arch [wp]:
  "\<lbrace>valid_arch_state'\<rbrace> setObject p (v::pde) \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  by (rule valid_arch_state_lift') (wp setObject_typ_at')+

lemma setObject_PTE_valid_arch [wp]:
  "\<lbrace>valid_arch_state'\<rbrace> setObject p (v::pte) \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  by (rule valid_arch_state_lift') (wp setObject_typ_at')+

lemma setObject_ASID_ct [wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> setObject p (e::asidpool) \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  apply (simp add: setObject_def updateObject_default_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_PDE_ct [wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> setObject p (e::pde) \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  apply (simp add: setObject_def updateObject_default_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_pte_ct [wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> setObject p (e::pte) \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  apply (simp add: setObject_def updateObject_default_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_ASID_cur_tcb' [wp]:
  "\<lbrace>\<lambda>s. cur_tcb' s\<rbrace> setObject p (e::asidpool) \<lbrace>\<lambda>_ s. cur_tcb' s\<rbrace>"
  apply (simp add: cur_tcb'_def)
  apply (rule hoare_lift_Pf [where f=ksCurThread])
   apply wp+
  done

lemma setObject_PDE_cur_tcb' [wp]:
  "\<lbrace>\<lambda>s. cur_tcb' s\<rbrace> setObject p (e::pde) \<lbrace>\<lambda>_ s. cur_tcb' s\<rbrace>"
  apply (simp add: cur_tcb'_def)
  apply (rule hoare_lift_Pf [where f=ksCurThread])
   apply wp+
  done

lemma setObject_pte_cur_tcb' [wp]:
  "\<lbrace>\<lambda>s. cur_tcb' s\<rbrace> setObject p (e::pte) \<lbrace>\<lambda>_ s. cur_tcb' s\<rbrace>"
  apply (simp add: cur_tcb'_def)
  apply (rule hoare_lift_Pf [where f=ksCurThread])
   apply wp+
  done



lemma pde_at_aligned_vptr':
  "\<lbrakk>x \<in> set [0 , 4 .e. 0x3C]; page_directory_at' pd s; is_aligned vptr 24 \<rbrakk> \<Longrightarrow>
  pde_at' (x + lookup_pd_slot pd vptr) s"
  apply (simp add: lookup_pd_slot_def Let_def page_directory_at'_def add.commute add.left_commute)
  apply (clarsimp simp: upto_enum_step_def)
  apply (clarsimp simp: shiftl_t2n)
  apply (subst mult.commute)
  apply (subst ring_distribs [symmetric])
  apply (erule allE)
  apply (erule impE)
   prefer 2
   apply assumption
  apply (erule (1) pde_shifting)
  done

lemma page_directory_pde_at_lookupI':
  "page_directory_at' pd s \<Longrightarrow> pde_at' (lookup_pd_slot pd vptr) s"
  apply (simp add: lookup_pd_slot_def Let_def)
  apply (erule page_directory_pde_atI')
  apply (rule vptr_shiftr_le_2p)
  done

lemma pt_bits_stuff:
  "pt_bits = ptBits"
  "ptBits < word_bits"
  "2 \<le> ptBits"
  by (simp add: pt_bits_def ptBits_def pageBits_def word_bits_def pteBits_def)+

lemma page_table_pte_at_lookupI':
  "page_table_at' pt s \<Longrightarrow> pte_at' (lookup_pt_slot_no_fail pt vptr) s"
  apply (simp add: lookup_pt_slot_no_fail_def)
  apply (erule page_table_pte_atI')
  apply (rule vptr_shiftr_le_2pt[simplified pt_bits_stuff])
  done

lemma storePTE_ctes [wp]:
  "\<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> storePTE p pte \<lbrace>\<lambda>_ s. P (ctes_of s)\<rbrace>"
  apply (rule ctes_of_from_cte_wp_at [where Q=\<top>, simplified])
  apply (rule storePTE_cte_wp_at')
  done

lemma storePDE_ctes [wp]:
  "\<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> storePDE p pte \<lbrace>\<lambda>_ s. P (ctes_of s)\<rbrace>"
  apply (rule ctes_of_from_cte_wp_at [where Q=\<top>, simplified])
  apply (rule storePDE_cte_wp_at')
  done


lemma storePDE_valid_objs [wp]:
  "\<lbrace>valid_objs' and valid_pde' pde\<rbrace> storePDE p pde \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (simp add: storePDE_def doMachineOp_def split_def)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps|wpc|simp)+
   apply (rule setObject_valid_objs')
   prefer 2
   apply assumption
  apply (clarsimp simp: updateObject_default_def in_monad)
  apply (clarsimp simp: valid_obj'_def)
  done

lemma setObject_ASID_cte_wp_at'[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at' P' p s)\<rbrace>
     setObject ptr (asid::asidpool)
   \<lbrace>\<lambda>rv s. P (cte_wp_at' P' p s)\<rbrace>"
  apply (wp setObject_cte_wp_at2'[where Q="\<top>"])
    apply (clarsimp simp: updateObject_default_def in_monad
                          projectKO_opts_defs projectKOs)
   apply (rule equals0I)
   apply (clarsimp simp: updateObject_default_def in_monad
                         projectKOs projectKO_opts_defs)
  apply simp
  done

lemma setObject_ASID_ctes_of'[wp]:
  "\<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>
     setObject ptr (asid::asidpool)
   \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  by (rule ctes_of_from_cte_wp_at [where Q=\<top>, simplified]) wp

lemma loadWordUser_inv :
  "\<lbrace>P\<rbrace> loadWordUser p \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding loadWordUser_def
  by (wp dmo_inv' loadWord_inv stateAssert_wp | simp)+

lemma clearMemory_vms':
  "valid_machine_state' s \<Longrightarrow>
   \<forall>x\<in>fst (clearMemory ptr bits (ksMachineState s)).
      valid_machine_state' (s\<lparr>ksMachineState := snd x\<rparr>)"
  apply (clarsimp simp: valid_machine_state'_def
                        disj_commute[of "pointerInUserData p s" for p s])
  apply (drule_tac x=p in spec, simp)
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = 0"
         in use_valid[where P=P and Q="\<lambda>_. P" for P], simp_all)
  apply (rule clearMemory_um_eq_0)
  done

lemma ct_not_inQ_ksMachineState_update[simp]:
  "ct_not_inQ (s\<lparr>ksMachineState := v\<rparr>) = ct_not_inQ s"
  by (simp add: ct_not_inQ_def)

lemma ct_in_current_domain_ksMachineState_update[simp]:
  "ct_idle_or_in_cur_domain' (s\<lparr>ksMachineState := v\<rparr>) = ct_idle_or_in_cur_domain' s"
  by (simp add: ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)

lemma dmo_clearMemory_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (clearMemory w sz) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  apply (clarsimp simp: invs'_def valid_state'_def)
  apply (rule conjI)
   apply (simp add: valid_irq_masks'_def, elim allEI, clarsimp)
   apply (drule use_valid)
     apply (rule no_irq_clearMemory[simplified no_irq_def, rule_format])
    apply simp_all
  apply (drule clearMemory_vms')
  apply fastforce
  done

end
end
